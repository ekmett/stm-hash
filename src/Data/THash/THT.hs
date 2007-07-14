---------------------------------------------------------------------------
-- |
-- Module      :  Data.THash.THT
-- Copyright   :  (C) 2006 Edward Kmett
-- License     :  BSD-style (see the file libraries/base/LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable (requires STM)
--
-- "Data.THash" Internals. Unless you really want to do the plumbing yourself
-- you probably want to use that instead.
-- 
-- There is a nearby point in the design space that generates a traditional
-- sorted linear hash table which will output keys and values in the same 
-- order as long as both hashes have the same set of keys, regardless of 
-- insertion order. To get there we would need to maintain the linked lists 
-- in sorted order.
----------------------------------------------------------------------------

module Data.THash.THT (
    THT,     -- Eq key => THT key value
    new,     -- (k -> Int) ->                              STM (THT k v)
    fromList,-- Eq k => (k -> Int) -> [(k,v)] ->           STM (THT k v)
    insert,  -- Eq k => THT k v -> k -> v ->               STM (THT k v, Bool)
    update,  -- Eq k => THT k v -> k -> v ->               STM (THT k v)
    modify,  -- Eq k => THT k v -> k -> (Maybe v -> v) ->  STM (THT k v)
    delete,  -- Eq k => THT k v -> k ->                    STM (THT k v, Bool)
    lookup,  -- Eq k => THT k v -> k ->                    STM (Maybe v)
    mapH,    --((k,v) -> r) -> THT k v ->                  STM [r]
    each,    -- THT k v ->                                 STM [(k,v)]
    keys,    -- THT k v ->                                 STM [k]
    values   -- THT k v ->                                 STM [v]
) where 

import Prelude
    ( Show(..), Ord(..), Eq, Bool(..), Maybe(..)
    , Num, Int
    , (*), (+), (-), ($), (==), (++), (.), (/=)
    , mapM_, sequence_, sequence, return, mod, fst, snd, id
    , otherwise
    )
import Data.Array
import Control.Monad (liftM, replicateM)
import Control.Concurrent.STM
import Control.Concurrent.STM.TVar
import qualified Data.List as List (partition, lookup, length, concatMap, map)
import Foreign (unsafePerformIO)

data THT k v = MkTHT
    { key_count   :: !Int
    , slots       :: Array Int (TVar [(k, v)])
    , split_ptr   :: !Int
    , max_split   :: !Int
    , hash        :: k -> Int
    }

{-# INLINE new #-}
new :: (k -> Int) -> STM (THT k v)
new hash = do 
    slots <- replicateM 4 $ newTVar []
    return MkTHT
        { key_count = 0
        , slots     = listArray (0,3) slots
        , split_ptr = 0
        , max_split = 1
        , hash      = hash 
        }

{-# INLINE fromList #-}
fromList :: Eq k => (k -> Int) -> [(k,v)] -> STM(THT k v)
fromList hash list = do
    slots <- replicateM max2 $ newTVar []
    let this = MkTHT
            { key_count = len
            , slots     = listArray (0,max2-1) slots
            , split_ptr = 0
            , max_split = max
            , hash      = hash
            }
        put (key,value) = do
            let loc = chain this key
            list <- readTVar loc
            writeTVar loc $ (key,value):list
    mapM_ put list
    return this
    where
    len = List.length list 
    max = p2 1
    max2 = max*2
    p2 m | len < m   = m
         | otherwise = p2 (m+m)

{-# INLINE split #-}
split :: THT k v -> STM (THT k v)
split this
    | old + 1 < max
    = split' this { split_ptr = old + 1 }
    | len < 2
    = return this
    | otherwise
    = do slots' <- grow $ slots this
         split' this 
            { split_ptr = max
            , max_split = max + max
            , slots     = slots'
            }
    where 
    old = split_ptr this
    max = max_split this
    len = key_count this
    new = old + max
    split' this' = do 
        list <- readTVar $ slots this' ! old
        let bin'    = bin this'
            (ol,nl) = List.partition (\(k,v) -> old == (locate this' k)) list
        writeTVar (slots this' ! old) ol -- reverse ol?
        writeTVar (slots this' ! new) nl -- reverse nl?
        return this'
            
{-# INLINE merge #-}
merge :: THT k v -> STM (THT k v)
merge this
    | split_ptr this /= 0
    = merge' this{ split_ptr = split_ptr this - 1 }
    | key_count this < 1
    = return this
    | otherwise
    = merge' this
        { max_split = m + m
        , split_ptr = m - 1 
        }
    where
    m = max_split this
    merge' this' = do
        ol <- readTVar $ ov
        nl <- readTVar $ nv
        writeTVar nv (ol ++ nl) -- merge and reverse?
        writeTVar ov []
        return this'
        where
        new = split_ptr this'
        max = max_split this'
        old = new + max
        v = slots this'
        ov = v ! old
        nv = v ! new
    
{-# INLINE lookup #-}
lookup :: Eq k => THT k v -> k -> STM (Maybe v)
lookup this key = if (key_count this == 0) 
    then return Nothing
    else do
    list <- readTVar $ chain this key
    return $ List.lookup key list

{-# INLINE insert #-}
insert :: Eq k => THT k v -> k -> v -> STM (THT k v, Bool)
insert this key value = do
    list <- readTVar $ chain this key
    case List.lookup key list of 
        Just _ -> return (this,False)
        (Nothing) -> do
            this' <- split this
            let tvar = chain this' key
            list' <- readTVar tvar
            writeTVar tvar $ (key,value):list'
            return (this',True)

{-# INLINE update #-}
update :: Eq k => THT k v -> k -> v -> STM (THT k v)
update this key value = modify this key $ \_ -> value

{-# INLINE modify #-}
modify :: Eq k => THT k v -> k -> (Maybe v -> v) -> STM (THT k v)
modify this key f = do
    list <- readTVar old
    case List.lookup key list of 
        Just value -> do 
            writeTVar old $ List.map fixup list 
            return this
        Nothing -> liftM fst . insert this key . f $ Nothing
    where
    old = chain this key
    fixup (k,v) | k == key  = (k, f $ Just v)
                | otherwise = (k, v)

{-# INLINE delete #-}
delete :: Eq k => THT k v -> k -> STM (THT k v, Bool)
delete this key = do 
    let tvar = chain this key
    list <- readTVar $ tvar
    case strip key list of 
        (list', True) -> do 
            writeTVar tvar list'
            this' <- merge this
            return (this', True)
        (_, False) -> return (this, False)

{-# INLINE strip #-}
strip :: Eq k => k -> [(k,v)] -> ([(k,v)],Bool)
strip key list = strip' key list []

strip' :: Eq k => k -> [(k,v)] -> [(k,v)] -> ([(k,v)],Bool)
strip' key ((key',val):tail) head
    | key == key'   = (head ++ tail, True) -- delete
    | otherwise     = strip' key tail $ (key',val):head
strip' _ [] head = (head, False) 

{-# INLINE grow #-}
-- replace a numerically indexed array of TVars of lists with one twice its size.
grow :: (Ix i, Num i) => Array i (TVar [t]) -> STM (Array i (TVar [t]))
grow a = do
    top <- replicateM n $ newTVar []
    return $ listArray (l,h') $ elems a ++ top
    where
    (l,h) = bounds a
    l' = h + 1
    h' = l' + h - l
    n = rangeSize(l',h')
        
{-# INLINE bin #-}
-- figure out what bin a given hashed value is mapped to.
bin :: THT k v -> Int -> Int
bin this val
    | x < split_ptr this = val `mod` (m+m)
    | otherwise          = x
    where
    x = val `mod` m 
    m = max_split this

{-# INLINE locate #-}
-- translate a key to its current bin
locate :: THT k v -> k -> Int
locate this key = bin this $ hash this key

{-# INLINE chain #-}
-- translate a key to a tvar in which we might find it
chain :: THT k v -> k -> TVar [(k,v)]
chain this key = slots this ! locate this key

{-# INLINE mapH #-}
mapH :: ((k,v) -> r) -> THT k v -> STM [r]
mapH f this = do 
    lists <- sequence [ readTVar $ slots this ! i | i <- [0,key_count this] ]
    return $ List.concatMap (List.map f) lists
    
{-# INLINE each #-}
each :: THT k v -> STM [(k,v)]
each = mapH id 

{-# INLINE keys #-}
keys :: THT k v -> STM [k]
keys = mapH fst

{-# INLINE values #-}
values :: THT k v -> STM [v]
values = mapH snd

