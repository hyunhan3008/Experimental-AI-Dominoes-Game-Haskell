{-
  Advanced Programming techniques COM2001
  Assignment2: Domino Games
  Made by Hyun HAN, 
-}
module Assignment2 where
  
  --For randomising and merging function
  import System.Random
  import MergeSort 
  
  --type definitions
  type Domino = (Int, Int)
  type Hand = [Domino]
  {- head of board is left end, last is right end. Order maintained e.g [(1,6),(6,6),(6,3),(3,1)] -}
  type Board = [Domino]
  --left or right end
  data End = L | R deriving (Eq, Show)
  --Return the domino which will go on L or R
  type DomsPlayer = Hand -> Board -> (Domino,End)
  --list of all dominoes as a constant with highest pip first i.e. (6,1) not (1,6)
  ordered = [(n,m)| n<-[0..6], m<-[0..6], m<=n] :: [Domino]
  
  --shuffle ordered set of dominoes with seed n
  shuffleDoms :: Int -> Hand
  shuffleDoms n = map fst ( mergesort (\(_,n1) (_,n2)->n1<n2) (zip ordered (take 28 (randoms (mkStdGen n):: [Int]))) )
  
  --simplePlayer take the first domino in hand which will go or the domino that is nonsense to be played like (100,100)
  simplePlayer :: DomsPlayer
  simplePlayer [] _ = ((100,100),L) --if no dominoes that can go, return unreasonable domino so it can't be played
  simplePlayer hand board
       | isJust lres = (fd, L) --domino which will go on L
       | isJust rres = (fd, R) --domino which will go on R
       | otherwise = simplePlayer rest board --Check all dominoes on hand
       where 
       (fd:rest) = hand
       lres = playDom fd board L
       rres = playDom fd board R
  
  --return true if maybe function have the maybe value
  isJust :: (Maybe a) -> Bool
  isJust (Just _) = True
  isJust Nothing = False
  
  --get the maybe result
  resMaybe :: (Maybe a)->a
  resMaybe (Just x) = x  
 
  -- If the domino can be played on the board, update the board.
  -- If nothing can be played, then return nothing 
  playDom :: Domino->Board->End->Maybe Board
  playDom domino [] _ = Just [domino] --if the board is empty, just play the domino on the board at first
  playDom domino board end
       -- dominio which will go on L, and update the board
       -- using playedp, check the domio is aleady played or not
       | ((end == L) && (lpip == v) && (playedP domino board == False)) = Just ((p,v) : board)
       -- Swap the pip position of the domino to fit in the board in the right order
       | ((end == L) && (lpip == p)&& (playedP domino board == False)) = Just ((v,p) : board)
       -- Same step as above for R side
       | ((end == R) && (rpip == p)&& (playedP domino board == False)) = Just (board ++ [(p,v)])
       | ((end == R) && (rpip == v)&& (playedP domino board == False)) = Just (board ++ [(v,p)])
       | otherwise = Nothing -- domino can't be played
       where
       (p,v) = domino
       ((lpip,_):_) = board
       (_,rpip) = last board
  
  --is domino played already?, so the same domino can't be plaeyd twice
  playedP :: Domino->Board-> Bool
  playedP domino@(p,v) board =(elem domino board || elem (v,p) board)
  
  --Return the domion which will make the higest score with proper L or R or domino that couldn't be played
  hsdPlayer :: DomsPlayer
  --No need to chcek empty hand
  --scoreN will return the domino that can't be played when no dominoes in hand can be plaeyd
  hsdPlayer hand board =
        let hiD = foldr (\ dom1 dom2 ->
                         if (fst(scoreN board dom1)) > (fst(scoreN board dom2))
                            then dom1 else dom2)
                         (head hand) (tail hand)
            direction = snd(scoreN board hiD) -- to know the domion can be played L or R?
        in (hiD, direction)
  
  --play the domino which will go on board, and return the score with L or R
  scoreN :: Board -> Domino-> (Int, End)
  scoreN board domino
       | isJust lres = (scoreBoard (resMaybe lres),L)
       | isJust rres = (scoreBoard (resMaybe rres),R)
       | otherwise = ((-1),L) -- To return the domino that can't be played
       where 
       lres = playDom domino board L
       rres = playDom domino board R
  
  --(from Assignment1), calculate the score of given board
  scoreBoard :: Board -> Int
  scoreBoard board
       -- When there is no domino with same element like (5,5) on the both end, check for 3s score
       -- When there is no domino with same element on the both end, no need to think about the case of dividing 5,
       -- because common factor of 3,5 is 15 and 12 is the maximum number without same element domino at the end
       | ( (mod (lpip+rpip) 3 == 0) && (lpip /= snd(head board)) && (rpip /= fst(last board)) ) = (lpip+rpip) `div` 3
       -- Same as above but just for case with divding by 5
       | ( (mod (lpip+rpip) 5 == 0) && (lpip /= snd(head board)) && (rpip /= fst(last board)) ) = (lpip+rpip) `div` 5
       -- Two code lines below are for the case of one domino on the board
       -- If there is one domino the sum can't be divided by both 3 and 5
       | ( (mod (lpip+rpip) 3 == 0) && (length board == 1) ) = (lpip+rpip) `div` 3
       | ( (mod (lpip+rpip) 5 == 0) && (length board == 1) ) = (lpip+rpip) `div` 5
       -- When the first domino of the board has the same two elements, then the left end should be doubled
       -- case for dividing with 3
       | ( (lpip == snd(head board)) && (length board > 1) && ( mod ((lpip*2)+rpip) 3 == 0) && ( mod ((lpip*2)+rpip) 5 /= 0) ) = ((lpip*2)+rpip) `div` 3
       -- Same as above but just the case for dividing with 5
       | ( (lpip == snd(head board)) && (length board > 1) && ( mod ((lpip*2)+rpip) 5 == 0) && ( mod ((lpip*2)+rpip) 3 /= 0) ) = ((lpip*2)+rpip) `div` 5
       -- Same as above but just the case for dividing bot 3 and 5
       | ( (lpip == snd(head board)) && ( mod ((lpip*2)+rpip) 3 == 0) && ( mod ((lpip*2)+rpip) 5 == 0) ) = ( (((lpip*2)+rpip) `div` 3) + (((lpip*2)+rpip) `div` 5) )
       -- Three lines below has exactly same structure for three lines above
       | ( (rpip == fst(last board)) && (length board > 1) && ( mod (lpip+(rpip*2)) 3 == 0) && ( mod (lpip+(rpip*2)) 5 /= 0) ) = (lpip+(rpip*2)) `div` 3
       | ( (rpip == fst(last board)) && (length board > 1) && ( mod (lpip+(rpip*2)) 5 == 0) && ( mod (lpip+(rpip*2)) 3 /= 0) ) = (lpip+(rpip*2)) `div` 5
       | ( (rpip == fst(last board)) && ( mod (lpip+(rpip*2)) 3 == 0) && ( mod (lpip+(rpip*2)) 5 == 0) ) = ( ((lpip+(rpip*2)) `div` 3) + ((lpip+(rpip*2)) `div` 5) )
       | otherwise = 0
       where 
       ((lpip,_):_) = board
       (_,rpip) = last board

  -- return list of tuples where fst is score for player1 and snd is for player2
  --If the player don't have domino to play then return (0,0) and end the game
  robby :: DomsPlayer->DomsPlayer->Board->Int->Int->[(Int,Int)]
  robby player1 player2 board seed repeat
       -- If the player1 have domino which can be played, play it and get the score on the left tuple
       --update the board and then call the secondPlayer by setting repeat=2
       --No need to update hand, playDom check the domino is played twice or not.
       | ((repeat==1) && (isJust resa)) = (scoreBoard (resMaybe resa),0):robby player1 player2 (resMaybe resa) seed 2
       -- If the player2 have domino which will go, play it and get the score on the left tuple
       | ((repeat==2) && (isJust resb)) = (0,scoreBoard (resMaybe resb)):robby player1 player2 (resMaybe resb) seed 1
       | otherwise = [(0,0)] -- If any of the players can't play the domino. 0 doesn't effect to the score
       where
       hand1 = take 9(shuffleDoms seed) -- take the first 9 cards of randomised set of dominoes
       hand2 = take 9(drop 9(shuffleDoms seed)) --take the next 9 cards 
       resa = playDom (fst(player1 hand1 board)) board (snd(player1 hand1 board)) -- player1 play the domino
       resb = playDom (fst(player2 hand2 board)) board (snd(player2 hand2 board)) -- player2 play the domion
  
  --using robby fns, return a two ints->summing fst values of tuples for fst player/ summing snd values of tuples for snd player
  playDomsRound :: DomsPlayer->DomsPlayer->Int->(Int, Int)
  playDomsRound player1 player2 seed = ((foldr (+) 0 (map fst res)),(foldr (+) 0 (map snd res)))
       where
       res = robby player1 player2 [] seed 1 -- start with empty board.