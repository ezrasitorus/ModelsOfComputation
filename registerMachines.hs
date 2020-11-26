import Data.Maybe

type Register = Int
type Label = Int

data Instruction = HALT | Plus Register Label | Minus Register Label Label deriving (Eq, Show)

type State = [(Register, Int)]
type Program = [(Label, Instruction)]

runProgram :: Program -> State -> State
runProgram p s = runInstruction p ((fromJust . lookup 0) p) s

runProgramC :: (State, Program) -> State
runProgramC (s, p) = runProgram p s

runProgramLC :: Integer -> (State, Program) -> State
runProgramLC l (s, p) = runProgramL l p s

runProgramL :: Integer -> Program -> State -> State
runProgramL 0 _ s = s
runProgramL l p s = runProgramL' l ((fromJust . lookup 0) p) p s

runProgramL' :: Integer -> Instruction -> Program -> State -> State
runProgramL' 0 _ _ s = s
runProgramL' l i p s 
    | i == HALT = s
    | otherwise = runProgramL' (l - 1) i' p s'
    where
        (i', s') = updateAndGet p i s

runInstruction :: Program -> Instruction -> State -> State
runInstruction _ HALT s = s
runInstruction p i s = runInstruction p i' s'
    where (i', s') = updateAndGet p i s

updateAndGet :: Program -> Instruction -> State -> (Instruction, State)
updateAndGet p (Plus r l) s
    | isNothing r1v = (HALT, s)
    | isNothing i' = (HALT, s')
    | otherwise = (fromJust i', s')
    where
        r1v = lookup r s
        i' = lookup l p
        s' = map (\cell@(r', i) -> if (r' == r) then (r, 1 + fromJust r1v) else cell) s

updateAndGet p (Minus r l1 l2) s
    | isNothing r1v = (HALT, s)
    | 0 == fromJust r1v && isNothing l2i = (HALT, s)
    | 0 == fromJust r1v = (fromJust l2i, s)
    | isNothing l1i = (HALT, s')
    | otherwise = (fromJust l1i, s')
    where
        r1v = lookup r s
        [l1i, l2i] = map (flip lookup p) [l1, l2]
        s' = map (\cell@(r', i) -> if (r' == r) then (r, fromJust r1v - 1) else cell) s


doub :: Int -> Int -> Int
doub x y = (2 ^ x) * (2 * y  + 1)

doubInverse :: Int -> (Int, Int)
doubInverse n
    = (m, div (q - 1) 2)
    where
        m = maxPowOf2 n
        q = div n (2 ^ m)
        

sing :: Int -> Int -> Int
sing x y = doub x y - 1

singInverse :: Int -> (Int, Int)
singInverse n
    = (m, div (q - 1) 2)
        where
            m = maxPowOf2 (n + 1)
            q = div (n + 1) (2 ^ m)

convertInstruction :: Instruction -> Int
convertInstruction HALT = 0
convertInstruction (Plus x l) = doub (2 * x) l
convertInstruction (Minus x l1 l2) = doub (2 * x + 1) (sing l1 l2)

maxPowOf2 :: Int -> Int
maxPowOf2 n
    | r == 1 = 0
    | otherwise = 1 + maxPowOf2 q
    where
        (q, r) = quotRem n 2

convertNumber :: Int -> Instruction
convertNumber 0 = HALT
convertNumber e
    | even m = Plus r e2
    | otherwise = Minus r o1 o2
    where
        m = maxPowOf2 e
        (e1, e2) = doubInverse e
        (o1, o2) = singInverse e2
        r = div e1 2

encode :: Program -> (Int, Int)
encode p =  ((convertInstruction . snd . head) p, foldr1 doub $ map (convertInstruction . snd) (tail p))

decode :: Int -> Int -> Program
decode x y = (0, convertNumber x) : zip [1..] (map convertNumber ns)
    where 
        ns = map fst $ getDoubPattern y

getDoubPattern :: Int -> [(Int, Int)]
getDoubPattern 0 = [(0, 0)]
getDoubPattern n = dp : getDoubPattern n'
        where
            dp@(_, n') = doubInverse n