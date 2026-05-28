{-# LANGUAGE BangPatterns #-}

-- | Union-find on the rubber-sheet substrate.
--
--   A 'Sheet' tracks a set of 'Place's that have been merged via 'unify',
--   together with optional /pinned info/ at each equivalence class
--   representative.  For v0 the info is a concrete universe 'Lv', merged by
--   equality.  For the later type-inference rehearsal the info will become a
--   type expression and the merge will be structural unification — the
--   shape of the structure here doesn't change, only the 'merge' function
--   passed in does.
--
--   Every 'Place' also carries a 'placeOffset' — a deck-shift slot on the
--   covering space, always 'Z' in v0 (no universe polymorphism yet) but
--   structurally present so v1 can fill it without rewriting the substrate.
module Constructor.Sheet
  ( Place (..)
  , Sheet
  , emptySheet
  , freshPlace
  , unify
  , pin
  , levelOf
  ) where

import Constructor.Level (Lv (..))
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM

-- | A place on the sheet — a node in the syntactic graph, with a level
--   offset (deck-shift) that is uniformly 'Z' in v0.
data Place = Place
  { placeId     :: !Int
  , placeOffset :: !Lv
  } deriving (Eq, Ord, Show)

-- | A sheet is a union-find forest plus a partial map of pinned info at
--   roots.  Parameterised in @info@ so the same structure carries levels
--   in v0 and type expressions later.
data Sheet info = Sheet
  { sheetNext  :: !Int
  , sheetParent :: !(IntMap Int)        -- non-root pid → root pid
  , sheetInfo   :: !(IntMap info)       -- root pid → pinned info
  } deriving Show

emptySheet :: Sheet info
emptySheet = Sheet 0 IM.empty IM.empty

-- | Allocate a fresh place.  v0 sets 'placeOffset' to 'Z'; v1 will compute
--   it based on the declaration's universe-polymorphism binders.
freshPlace :: Sheet info -> (Place, Sheet info)
freshPlace s = (Place (sheetNext s) Z, s { sheetNext = sheetNext s + 1 })

-- | Find with path compression.  Returns the root's id and the updated sheet.
findId :: Int -> Sheet info -> (Int, Sheet info)
findId pid s = case IM.lookup pid (sheetParent s) of
  Nothing -> (pid, s)
  Just parent ->
    let (root, s') = findId parent s
        s'' | root == parent = s'
            | otherwise = s' { sheetParent = IM.insert pid root (sheetParent s') }
    in (root, s'')

-- | Unify two places into the same equivalence class.  The 'merge' callback
--   resolves two pinned infos:
--
--     * If only one side is pinned, that pin survives.
--     * If both sides are pinned, 'merge' decides (e.g., equality check for
--       'Lv'; recursive structural unification for type expressions).
unify
  :: (info -> info -> Either err info)
  -> Place
  -> Place
  -> Sheet info
  -> Either err (Sheet info)
unify merge a b s0 =
  let (ra, s1) = findId (placeId a) s0
      (rb, s2) = findId (placeId b) s1
  in if ra == rb
       then Right s2
       else case (IM.lookup ra (sheetInfo s2), IM.lookup rb (sheetInfo s2)) of
              (Just ia, Just ib) -> do
                merged <- merge ia ib
                Right $ link ra rb (Just merged) s2
              (Just ia, Nothing) -> Right $ link ra rb (Just ia) s2
              (Nothing, Just ib) -> Right $ link ra rb (Just ib) s2
              (Nothing, Nothing) -> Right $ link ra rb Nothing  s2
  where
    -- Point @ra@ at @rb@; install (or clear) the pinned info on @rb@.
    link ra rb mInfo s =
      s { sheetParent = IM.insert ra rb (sheetParent s)
        , sheetInfo   = case mInfo of
            Just info -> IM.insert rb info (IM.delete ra (sheetInfo s))
            Nothing   ->                       IM.delete ra (sheetInfo s)
        }

-- | Pin a place's representative to concrete info.  'merge' resolves conflict
--   if the rep was already pinned.
pin
  :: (info -> info -> Either err info)
  -> Place
  -> info
  -> Sheet info
  -> Either err (Sheet info)
pin merge p info s0 =
  let (root, s1) = findId (placeId p) s0
  in case IM.lookup root (sheetInfo s1) of
       Nothing -> Right (s1 { sheetInfo = IM.insert root info (sheetInfo s1) })
       Just existing -> do
         merged <- merge existing info
         Right (s1 { sheetInfo = IM.insert root merged (sheetInfo s1) })

-- | Read the pinned info of a place's representative, if any.
levelOf :: Place -> Sheet info -> (Maybe info, Sheet info)
levelOf p s0 =
  let (root, s1) = findId (placeId p) s0
  in (IM.lookup root (sheetInfo s1), s1)
