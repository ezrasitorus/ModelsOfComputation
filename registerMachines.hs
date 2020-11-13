import Data.Maybe

type Register = Int
type Label = Int

data Instruction = HALT | Plus Register Label | Minus Register Label Label deriving (Eq)

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

example :: (State, Program)
example = ([(0, 0), (1, 1), (2, 2)], [(0, Minus 1 1 2), (1, Plus 0 0), (2, Minus 2 3 4), (3, Plus 0 2), (4, HALT)])

nonHaltExample :: (State, Program)
nonHaltExample = ([(0, 0)], [(0, Plus 0 0)])