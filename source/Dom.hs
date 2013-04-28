module Dom where

import Type
import List (union)

class Dom a where
  dom:: a -> [Id]

instance Dom a => Dom [a] where
  dom = foldr (union.dom) []
