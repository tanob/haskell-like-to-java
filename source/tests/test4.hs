{
{-
x :: Int;
x = 1;

s :: [Char];
s = "hello";
-}

data Maybe a = Just a | Nothing;

-- Se colocar: f :: Int -> Int o inferidor deixa passar ...
-- f :: Maybe a -> Int;
f (Just x) = x;
f (Nothing) = 0;
}