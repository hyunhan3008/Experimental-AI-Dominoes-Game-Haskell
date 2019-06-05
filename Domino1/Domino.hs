-- Assignment 1
-- Written by Hyun HAN
module Domino where
  
  -- Domino is a tuple which contains two integers
  type Domino = (Int, Int)
  type Hand = [Domino] 
  type Board = [Domino]
  -- L and R indicate the direction of the each end side of the board
  data End = L | R deriving (Eq, Show)

  -- Given domino and end and board, check that the domino can be put on the end of the board
  goesP :: Domino -> End -> Board -> Bool
  goesP domino end board
     | (end == L) = goesLeft domino board -- When end is L, check that domino can be put on the left
     | (end == R) = goesRight domino board -- same as above but for right end
     | otherwise = False
  
  -- Check that the domino can be put on the left end
  goesLeft :: Domino -> Board -> Bool
  goesLeft domino board
     -- If the any elements of the domino is same as fst element of the board(lpip), return true
     -- If the domino contains at least one 0 element, it can be always fit in the board, so return true
     | (fst domino == lpip) || (snd domino == lpip) = True
     | otherwise = False
     where
     ((lpip,_):_) = board -- lpip is the first element of the first domino of the board
  
  -- Same with goesLeft but for the other direction
  goesRight :: Domino->Board-> Bool
  goesRight domino board
     | (fst domino == rpip) || (snd domino == rpip) = True
     | otherwise = False
     where 
     (_,rpip) = last board
  
  --Chek that any dominoes on hand can be played on the board. If nothing can be played then return true
  knockingP :: Board-> Hand -> Bool
  -- If there is nothing on hand, no dominoes can be fit in the board
  knockingP _ [] = True
  knockingP board hand
     -- if there is the domino which can be played at right or left end of the board, return false
     | ((goesLeft (h,t) board) == True) || (goesRight (h,t) board == True) = False
     | otherwise = knockingP board rest -- Iterate unitll checking all the dominoes cannot be played
     where 
     ((h,t):rest) = hand

  -- Check that the given domino is already played or not
  playedP :: Domino->Board-> Bool
  playedP domino board
     -- If the given domino is already on the board, it means the domino has been already plaeyd, so return true
     -- Element of the domino can be swapped each other
     | (elem (p,v) board == True || elem (v,p) board == True) = True
     | otherwise = False
     where
     (p,v) = domino

  -- When the board and hand is given, check the possible dominoes that can be played on the left or right end
  -- First lists of  the tuple is for dominoes that can be played on left end and the second lists of the tuple is for right end
  possPlay :: Board -> Hand -> ([Domino],[Domino])
  possPlay board hand
       -- When there are dominoes that can be played only on the leftend
       | ((possPlayL board hand /=[]) && (possPlayR board hand == [])) = (leftres,[])
       -- When there are dominoes that can be played only on the right end
       | ((possPlayL board hand ==[]) && (possPlayR board hand /= [])) = ([],rightres)
       -- When there are dominoes that can be played eiether on right or left end
       | ((possPlayL board hand /=[]) && (possPlayR board hand /= [])) = (leftres,rightres)
       | otherwise = ([],[])
       where 
       leftres = possPlayL board hand -- Get the list of dominoes that can played on the left end
       rightres = possPlayR board hand -- Get the list of dominoes that can be played on the right end
  
  possPlayL :: Board -> Hand -> [Domino]
  possPlayL _ [] = []
  possPlayL board hand
       -- Find all the dominoes that can be fit in the left end
       | ( (lpip==p) || (lpip==v) ) = (p,v):possPlayL board rest
       | otherwise = possPlayL board rest
       where 
       ((p,v):rest) = hand
       ((lpip,_):_) = board

  possPlayR :: Board -> Hand -> [Domino]
  possPlayR _ [] = []
  possPlayR board hand
       -- Find all the dominoes that can be fit in the right end
       | ( (rpip==p) || (rpip==v) ) = (p,v):possPlayR board rest
       | otherwise = possPlayR board rest
       where 
       ((p,v):rest) = hand
       (_,rpip) = last board

  -- If the domino can be played on the board, update the board.
  -- If nothing can be played, then return nothing
  playDom :: Domino->Board->End->Maybe Board
  playDom domino board end
       -- Check that the domino can be on the left end of the board, and update the board
       | ((end == L) && (lpip == v)) = Just ((p,v) : board)
       -- Swap the element position of the domino to fit in the board in the right order
       | ((end == L) && (lpip == p)) = Just ((v,p) : board)
       -- Same step for right side end
       | ((end == R) && (rpip == p)) = Just (board ++ [(p,v)])
       | ((end == R) && (rpip == v)) = Just (board ++ [(v,p)])
       | otherwise = Nothing
       where
       (p,v) = domino
       ((lpip,_):_) = board
       (_,rpip) = last board
 
  -- Check the board can make 5s-and-3s score. Check the sum of each end is divisable either by 3 or 5
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
  
  -- When the function return maybe result, return the true
  -- If maybe function returns nothing, then return False
  isJust :: (Maybe a) -> Bool
  isJust (Just _) = True
  isJust Nothing = False
  
  -- resMaybe is to get a maybe result from the maybe function
  resMaybe :: (Maybe a)->a
  resMaybe (Just x) = x
  
  -- If there are dominoes which can make score given integer n, then return that domino with the sign of the end type
  scoreN :: Board->Int->Hand->[(Domino,End)]
  scoreN board n [] = [] -- If there is nothing on the hand, then can make score anymore
  scoreN board n hand
       -- If the first domino on hand can be played on L by making socre n, return this domino with L sign
       -- Do the same step with dominoes left on the hand
       | (isJust lres && (scoreBoard (resMaybe lres)==n)) = (fd,L):scoreN board n rest
       -- This step is same as above but for right side end
       | (isJust rres && (scoreBoard (resMaybe rres)==n)) =(fd,R):scoreN board n rest
       | otherwise = scoreN board n rest -- check all the dominoes on the hand
       where 
       (fd:rest) = hand
       lres = playDom fd board L -- lres is the result that first domino can be played on the left end
       rres = playDom fd board R -- rres is the result that first domino can be played on the right end