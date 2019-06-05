{--
  Advanced Programming techniques COM2001
  Assignment3: Domino Games
  smartPlayer Made by Hyun HAN, 
--}
module Assignment3 where
 
 {- play a 5's & 3's singles match between 2 given players
    play n games, each game up to 61
 -}
 
 --import Doms
 import System.Random
 import Data.List
 import Debug.Trace
 
 type Dom = (Int,Int)
 -- with highest pip first i.e. (6,1) not (1,6)

 data DomBoard = InitBoard|Board Dom Dom History
                    deriving (Show)
 
 type History = [(Dom,Player,MoveNum)]
 -- History allows course of game to be reconstructed                                            
                                               
 data Player = P1|P2 -- player 1 or player 2
                  deriving (Eq,Show)
 
 data End = L|R -- left end or right end
                  deriving (Eq,Show)
 
 type MoveNum = Int

 type Hand = [Dom]
  
 -- the full set of Doms
 domSet :: [Dom]
 
 domSet = [(6,6),(6,5),(6,4),(6,3),(6,2),(6,1),(6,0),
                 (5,5),(5,4),(5,3),(5,2),(5,1),(5,0),
                       (4,4),(4,3),(4,2),(4,1),(4,0),
                             (3,3),(3,2),(3,1),(3,0),
                                   (2,2),(2,1),(2,0),
                                         (1,1),(1,0),
                                               (0,0)]
                                                                                         
 
 type Move = (Dom,End)
 type Scores = (Int,Int)
                                                                                              
 -- state in a game - p1's hand, p2's hand, player to drop, current board, scores 
 type GameState =(Hand,Hand,Player, DomBoard, Scores)
 
 
 ------------------------------------------------------
 {- DomsPlayer
    given a Hand, the Board, which Player this is and the current Scores
    returns a Dom and an End
    only called when player is not knocking
    made this a type, so different players can be created
 -}
 
 type DomsPlayer = Hand->DomBoard->Player->Scores->(Dom,End)
 
 {- variables
     hand h
     board b
     player p
     scores s
 -}

 -- example players
 -- randomPlayer plays the first legal dom it can, even if it goes bust
 randomPlayer :: DomsPlayer
 
 randomPlayer h b p s 
  |not(null ldrops) = ((head ldrops),L)
  |otherwise = ((head rdrops),R)
  where
   ldrops = leftdrops h b
   rdrops = rightdrops h b
   
 -- hsdplayer plays highest scoring dom, even if it goes bust
 -- we have  hsd :: Hand->DomBoard->(Dom,End)
 hsdPlayer :: DomsPlayer
 hsdPlayer h b p s = (d,e)
                     where (d,e)=hsd h b

  -- highest scoring dom

 hsd :: Hand->DomBoard->Move
 
 hsd h InitBoard = (md,L)
  where
   dscores = zip h (map (\ (d1,d2)->score53 (d1+d2)) h)
   (md,ms) = maximumBy (comparing snd) dscores
   
 hsd h b =
   let
    ld= leftdrops h b
    rd = rightdrops h b
    lscores = zip ld (map (\d->(scoreDom d L b)) ld) -- [(Dom, score)]
    rscores = zip rd (map (\d->(scoreDom d R b)) rd)
    (lb,ls) = if (not(null lscores)) then (maximumBy (comparing snd) lscores) else ((0,0),-1) -- can't be chosen
    (rb,rs) = if (not(null rscores)) then (maximumBy (comparing snd) rscores) else ((0,0),-1)
   in
    if (ls>=rs) then (lb,L) else (rb,R)
 
 --Minimise the chance of losing, and maximising the chance of winning
 smartPlayer :: DomsPlayer 

 --Two big case: one tactic befor score 53 and the other for after 53
 smartPlayer h b p s
  --Tactic for the end game
  | isJust (dom61 h p b s) = resMaybe (dom61 h p b s) -- check if can win in the next move
  | isJust (safe59 h h p b s) = resMaybe (safe59 h h p b s) -- doms to 59 which not lead to opponent win
 --If both players score <53 then, it is better to get higher score dom than the opponent may score (which is in smt function)
  | (((oppscore>=53) || (myscore>=53)) && (isJust (noBust h h p b s))) = resMaybe (noBust h h p b s) -- not exceed 61 dom which not lead to opponent win
  --When my score>53, there can be a domino that exceed 61 but is sure that the opponent can't win -> Difference with noBust function
  | (((oppscore>=53) || (myscore>=53)) && (isJust (blocking h h b p s))) = resMaybe (blocking h h b p s) -- prevent the opponent to win in the next move
  | ((oppscore>=51) && isJust (prevent59 h h p b s)) = resMaybe (prevent59 h h p b s) -- prohibit the oppoonent to get 59 (59 is likely to win next time)
  | isJust (get59 h p b s) = resMaybe (get59 h p b s) -- nothing is sure so just try to get score 59 for the nextmove
  -- Tactic before the end game
  | otherwise = smt h b -- case both players score are less than 53
  where
   myscore = myS p s -- get my current score
   oppscore = opponentS p s -- get opponent current score
   ld = leftdrops h b
   rd = rightdrops h b
 
 --get higher score dom that does not lead to situation where the opponent score higher
 smt :: Hand->DomBoard->Move

 --When this player is the first starat of the game
 smt h InitBoard
  | ((elem (6,6) h) && (elem (6,3) h)) = ((6,6),L) -- safe and maximum score
  | elem (5,4) h = ((5,4),L) -- no dominoes that can score higher after this
  | otherwise = (md,L)
  where
   dscores = zip h (map (\ (d1,d2)->score53 (d1+d2)) h)
   (md,ms) = maximumBy (comparing snd) dscores

 --If i play a domino, after this if all the doms that can score higher than before are on smt hand and board, then the domino is safe
 smt h b
  | isJust (safeDomino h h b) = resMaybe (safeDomino h h b) -- If there are any safe doms
  | isJust (morechance h h b) = resMaybe (morechance h h b) -- 70% safe doms
  | otherwise = hsd h b -- If no case aobve, just get highest scoring dom
 
 -- play the highest score dom(A) and update the board, after that, get all the possible dominoes that can make higher score with updated board
 -- If all these dominoes either on my hand or board, then return dom(A). 
 -- The reason of Hand written twice is one for recursion, the other for guessing the opponent's hand
 -- validHand is needed beceause domino is deleted after every recursion.
 safeDomino :: Hand->Hand->DomBoard->Maybe (Dom,End)
 safeDomino h h2 b
  | ((length (validHand h b)>=1) && (safeCheck checkList (h2++(getBoard b))))  = Just (d, e) -- This domino is surely the highest dom that can go curretnly
  | (length (validHand h b) == 0) = Nothing --No dominoes is safe
  | otherwise = safeDomino (delete d h) h2 b -- get the next domino and test it is safe or not agian untill nothing can be played
  where
   (d,e)= hsd h b
   nb = updateBoard d e P1 b -- player is not important
   (lPlays,rPlays) = possPlays domSet nb -- get all possible doms on the updated board
   allPlays = [( scoreboard ( playleft P1 d nb), d)|d<-lPlays]++   -- a play is (score, dom)      
              [( scoreboard ( playright P1 d nb), d)|d<-rPlays]
   checkList =  map snd (filter (\(n,_) ->  (n>(scoreDom d e b))) allPlays) -- all possible higher score doms than the score I made

  --If first Hand is part of second Hand, True. Otherwise False
 safeCheck :: Hand->Hand->Bool
 safeCheck [] _ = True
 safeCheck h@(f:t) h2
  |playedP f h2 = safeCheck t h2
  |otherwise = False

 --Play dom, (the number of higher score dom on the current board and hand)/(the total number of higher score dom) is safety percentage
 --Return the domino that is more than 70% percentage e.g 3/4 doms 4/5 doms 5/6 doms
 --Better than playing just highest score dom
 morechance :: Hand->Hand->DomBoard->Maybe Move
 morechance h h2 b
  -- need to check wheter there is a domino to play or not, because every recursion a domino is deleted from the hand
  | ((length (validHand h b)>=1) &&(not (null checkList)) &&(score >(0.7)) ) = Just (d,e)
  | (length (validHand h b)==0) = Nothing -- No high possiblity dominoes
  | otherwise = morechance (delete d h) h2 b --recurse untill the right dom is found
  where
   (d,e) = hsd h b -- get the highest dom
   nb = updateBoard d e P1 b
   (lPlays,rPlays) = possPlays domSet nb
   allPlays = [( scoreboard ( playleft P1 d nb), d)|d<-lPlays]++   -- this is (score, dom)      
              [( scoreboard ( playright P1 d nb), d)|d<-rPlays]
   checkList =  map snd (filter (\(n,_) ->  (n>scoreDom d e b)) allPlays) --get all doms that can make higher score than I can make (dangerous doms)
   addup = sum (issame checkList (h2++(getBoard b))) -- check how many dangerous doms are on hand or board
   score = ((fromIntegral addup)/(fromIntegral (length checkList))) -- Get the percentage

 --to check how many doms are identical between two hands
 --it will return 1s as much as the number of identical doms
 issame :: Hand->Hand->[Int]
 issame [] _ = []
 issame h@(f:t) h2
  | (playedP f h2) = 1:issame t h2
  | otherwise = issame t h2

 --Return all the possible movement
 --same as adding lPlays and rPlays
 validHand :: Hand->DomBoard->Hand
 validHand h b = lPlays++rPlays
  where
  (lPlays,rPlays) = possPlays h b

 --Extract dominoes that are played given DomBoard
 getBoard :: DomBoard->[Dom]
 getBoard InitBoard = []
 getBoard (Board d d2 hist) = [d|(d,_,_)<-hist]  
 
 -- If maybe function return value then true, Nothing->False
 isJust :: (Maybe a) -> Bool
 isJust (Just _) = True
 isJust Nothing = False
 
 -- Get the value from the maybe function
 resMaybe :: (Maybe a)->a
 resMaybe (Just x) = x  
 
 --Check to win
 dom61 :: Hand->Player->DomBoard->Scores->Maybe Move
 dom61 h p b s
  | not (null rightD) = Just (head rightD) -- get any dom that makes me score 61
  | otherwise = Nothing
  where
   myscore = myS p s -- my current score
   (lPlays,rPlays) = possPlays h b
   allPlays = [( scoreboard ( playleft P1 d b), (d,L))|d<-lPlays]++   --  is (score, dom)      
              [( scoreboard ( playright P1 d b), (d,R))|d<-rPlays]
   rightD = map snd (filter (\(n,_) -> (n==(61-myscore))) allPlays) -- filter doms out that can make 61

 --This is a function to get myscore from both player's score
 myS :: Player->Scores->Int
 myS p s@(a,b)
  | (p==P1) = a
  | (p==P2) = b 
  
 --This is a fucntion to get opponent's score
 opponentS :: Player->Scores->Int
 opponentS p s@(a,b)
  | p==P1 = b
  | p==P2 = a
  
 --Find the domino to 59 which not lead to opponent's win in the next move
 safe59 :: Hand->Hand->Player->DomBoard->Scores->Maybe Move
 safe59 h h2 p b s
  -- if there is a dom to 59 and if all the doms that make the opponent win on board++hand, then it is safe dom to play
  --When doing the safecheck, hand should be the intial hand given
  | ((not (null rightD)) && (safeCheck higherList (h2++(getBoard b)))) = Just (domino,end)
  | (null rightD) = Nothing -- there is no dom to 59 anymore
  | otherwise = safe59 (delete domino h) h2 p b s -- delete the domino
  where
   myscore = myS p s
   oppscore = opponentS p s
   (lPlays,rPlays) = possPlays h b
   allPlays = [( scoreboard ( playleft P1 d b), (d,L))|d<-lPlays]++   -- this is (score, dom)      
              [( scoreboard ( playright P1 d b), (d,R))|d<-rPlays]
   rightD = map snd (filter (\(n,_) -> (n==(59-myscore))) allPlays) -- get all the doms to 59
   (domino, end) = head rightD
   newb = updateBoard domino end P1 b
   (lPlays2,rPlays2) = possPlays domSet newb -- get all the possible doms that can be played on the updated board
   allPlayss = [( scoreboard ( playleft P1 d newb), d)|d<-lPlays2]++   --  (score, dom)
              [( scoreboard ( playright P1 d newb), d)|d<-rPlays2]
   higherList =  map snd (filter (\(n,_) -> (n==61-oppscore)) allPlayss) -- return all the doms that can make opponents to win (dangerous doms)
   
 -- Find the domino that not score over 61
 noBust :: Hand->Hand->Player->DomBoard->Scores->Maybe Move
 noBust h h2 p b s
  -- if there is dom that not go over 61 and if this does not lead to opponent's win then it is safe dom.
  | ( (length (validHand h b)>=1) && (scoreDom d e b<=(61-myscore)) && (safeCheck higherList (h2++(getBoard b)))) = Just (d,e)
  | (length (validHand h b)==0) = Nothing -- there is no dom that are fully safe
  | otherwise = noBust (delete d h) h2 p b s -- get the next dom that makes me score 59 and check safety again
  where
   myscore = myS p s
   oppscore = opponentS p s
   (d,e) = hsd h b
   newb = updateBoard d e P1 b
   (lPlays,rPlays) = possPlays domSet newb  -- get all the doms that can be played after i play
   allPlays = [( scoreboard ( playleft P1 d newb), d)|d<-lPlays]++   -- a play is (score, dom)      
              [( scoreboard ( playright P1 d newb), d)|d<-rPlays]
   higherList = map snd (filter (\(n,_) -> (n==(61-oppscore))) allPlays) -- doms that can make opponent to win if i play my dom

 -- find the dom that lead surely not to opponent's win in the next move
 blocking :: Hand->Hand->DomBoard->Player->Scores->Maybe Move
 blocking h h2 b p s
  -- if all the dangeours doms are on hand and board, then the domino is safe to go
  -- If so, my domino is safe to drop
  | ((length (validHand h b)>=1) &&(safeCheck higherList (h2++(getBoard b)))) = Just (d,e)
  | (length (validHand h b)==0) = Nothing
  | otherwise = blocking (delete d h) h2 b p s -- recurse untill there is no dominoes to play
  where
   oppscore = opponentS p s -- opponent score
   (d,e) = hsd h b
   nb = updateBoard d e P1 b
   (lPlays,rPlays) = possPlays domSet nb
   allPlays = [( scoreboard ( playleft P1 d nb), d)|d<-lPlays]++   -- this is (score, dom)      
              [( scoreboard ( playright P1 d nb), d)|d<-rPlays]
   higherList =  map snd (filter (\(n,_) ->  (n==(61-oppscore))) allPlays) -- get all the doms that make opponent win (dangerous doms)
   
 -- domino that make the score 59
 get59 :: Hand->Player->DomBoard->Scores->Maybe Move
 get59 h p b s
  -- if there is anything that makes me score 59
  | not (null ranList) = Just (d,e)
  | (null ranList) = Nothing -- there is no dom to 59
  where
   myscore= myS p s -- get my current score
   (lPlays,rPlays) = possPlays h b
   allPlays = [( scoreboard ( playleft P1 d b), (d,L))|d<-lPlays]++   -- a play is (score, dom)      
              [( scoreboard ( playright P1 d b), (d,R))|d<-rPlays]
   ranList = map snd (filter (\(n,_) -> (n==(59-myscore))) allPlays) -- get all the doms that can make the score to 59
   (d,e) = head ranList
 
 --prevent the opponent to get 59
 prevent59 :: Hand->Hand->Player->DomBoard->Scores->Maybe Move
 prevent59 h h2 p b s
  --If all the dangeours doms are on hand and board then the domino can prevent from the opponent to 59
  | ((length (validHand h b)>=1) &&(safeCheck higherList (h2++(getBoard b)))) = Just (d,e)
  | (length (validHand h b)==0) = Nothing
  | otherwise = prevent59 (delete d h) h2 p b s -- get the next dom that makes me score 59
  where
   oppscore= opponentS p s
   (d,e) = hsd h b
   nb = updateBoard d e P1 b
   (lPlays,rPlays) = possPlays domSet nb
   allPlays = [( scoreboard ( playleft P1 d nb), d)|d<-lPlays]++   -- this is (score, dom)      
              [( scoreboard ( playright P1 d nb), d)|d<-rPlays]
   higherList =  map snd (filter (\(n,_) ->  (n==(59-oppscore))) allPlays) -- all the doms to 61 after my move (dagnerous doms)
 
 -- functions from the past assginment
 -- returns all the possible dominoes that can go 
 possPlays :: Hand->DomBoard->(Hand,Hand)
 possPlays h b = (leftdrops h b, rightdrops h b)
 
 --check the domino is played or not, if played true
 playedP :: Dom->Hand-> Bool
 playedP domino@(p,v) board =(elem domino board || elem (v,p) board)
 -----------------------------------------------------------------------------------------
 {- top level fn
    args: 2 players (p1, p2), number of games (n), random number seed (seed)
    returns: number of games won by player 1 & player 2
    calls playDomsGames giving it n, initial score in games and random no gen
 -} 
 
 domsMatch :: DomsPlayer->DomsPlayer->Int->Int->(Int,Int)
 
 domsMatch p1 p2 n seed = playDomsGames p1 p2 n (0,0) (mkStdGen seed)
 
 -----------------------------------------------------------------------------------------
 
{- playDomsGames plays n games

  p1,p2 players
  (s1,s2) their scores
  gen random generator
-}
 
 playDomsGames :: DomsPlayer->DomsPlayer->Int->(Int,Int)->StdGen->(Int,Int)
 
 playDomsGames _ _ 0 score_in_games _ = score_in_games -- stop when n games played
 
 playDomsGames p1 p2 n (s1,s2) gen 
   |gameres==P1 = playDomsGames p1 p2 (n-1) (s1+1,s2) gen2 -- p1 won
   |otherwise = playDomsGames p1 p2 (n-1) (s1,s2+1) gen2 -- p2 won
  where
   (gen1,gen2)=split gen -- get 2 generators, so doms can be reshuffled for next hand
   gameres = playDomsGame p1 p2 (if (odd n) then P1 else P2) (0,0) gen1 -- play next game p1 drops if n odd else p2
 
 -----------------------------------------------------------------------------------------
 -- playDomsGame plays a single game - 61 up
 -- returns winner - P1 or P2
 -- the Bool pdrop is true if it's p1 to drop
 -- pdrop alternates between games
 
 playDomsGame :: DomsPlayer->DomsPlayer->Player->(Int,Int)->StdGen->Player
 
 playDomsGame p1 p2 pdrop scores gen 
  |s1==61 = P1
  |s2==61 = P2
  |otherwise = playDomsGame p1 p2 (if (pdrop==P1) then P2 else P1) (s1,s2) gen2
  where
   (gen1,gen2)=split gen
   (s1,s2)=playDomsHand p1 p2 pdrop scores gen1  
  
 -----------------------------------------------------------------------------------------
 -- play a single hand
  
 playDomsHand :: DomsPlayer->DomsPlayer->Player->(Int,Int)->StdGen->(Int,Int)
 
 playDomsHand p1 p2 nextplayer scores gen = 
   playDoms p1 p2 init_gamestate
  where
   spack = shuffleDoms gen
   p1_hand = take 9 spack
   p2_hand = take 9 (drop 9 spack)
   init_gamestate = (p1_hand,p2_hand,nextplayer,InitBoard,scores) 
   
 ------------------------------------------------------------------------------------------   
 -- shuffle 
 
 shuffleDoms :: StdGen -> [Dom]

 shuffleDoms gen =  
  let
    weights = take 28 (randoms gen :: [Int])
    dset = (map fst (sortBy  
               (\ (_,w1)(_,w2)  -> (compare w1 w2)) 
               (zip domSet weights)))
  in
   dset
   
 ------------------------------------------------------------------------------------------
 -- playDoms runs the hand
 -- returns scores at the end

 
 playDoms :: DomsPlayer->DomsPlayer->GameState->(Int,Int)
 
 playDoms _ _ (_,_,_,_, (61,s2)) = (61,s2) --p1 has won the game
 playDoms _ _ (_,_,_,_, (s1,61)) = (s1,61) --p2 has won the game
 
 
 playDoms p1 p2 gs@(h1,h2,nextplayer,b,scores)
  |(kp1 &&  kp2) = scores -- both players knocking, end of the hand
  |((nextplayer==P1) && (not kp1)) =  playDoms p1 p2 (p1play p1 gs) -- p1 plays, returning new gameState. p2 to go next
  |(nextplayer==P1) = playDoms p1 p2 (p2play p2 gs) -- p1 knocking so p2 plays
  |(not kp2) = playDoms p1 p2 (p2play p2 gs) -- p2 plays
  |otherwise = playDoms p1 p2 (p1play p1 gs) -- p2 knocking so p1 plays
  where
   kp1 = knocking h1 b -- true if p1 knocking
   kp2 = knocking h2 b -- true if p2 knocking
   
 ------------------------------------------------------------------------------------------
 -- is a player knocking?

 knocking :: Hand->DomBoard->Bool
 
 knocking h b = 
  ((null (leftdrops h b)) && (null (rightdrops h b))) -- leftdrops & rightdrops in doms.hs
 
 ------------------------------------------------------------------------------------------
   
 -- player p1 to drop
 
 p1play :: DomsPlayer->GameState->GameState
 
 p1play p1 (h1,h2,_,b, (s1,s2)) =
  ((delete dom h1), h2, P2,(updateBoard dom end P1 b), (ns1, s2))
   where
    (dom,end) = p1 h1 b P1 (s1,s2)-- call the player, returning dom dropped and end it's dropped at.
    score = s1+ (scoreDom dom end b) -- what it scored
    ns1 = if (score >61) then s1 else score -- check for going bust
    
 
 -- p2 to drop
   
 p2play :: DomsPlayer->GameState->GameState
 
 p2play p2 (h1,h2,_,b,(s1,s2)) =
  (h1, (delete dom h2),P1, (updateBoard dom end P2 b), (s1, ns2))
  where
   (dom,end) = p2 h2 b P2 (s1,s2)-- call the player, returning dom dropped and end it's dropped at.
   score = s2+ (scoreDom dom end b) -- what it scored
   ns2 = if (score >61) then s2 else score -- check for going bust
 
   -------------------------------------------------------------------------------------------
 -- updateBoard 
 -- update the board after a play
 
 updateBoard :: Dom->End->Player->DomBoard->DomBoard
 
 updateBoard d e p b
  |e==L = playleft p d b
  |otherwise = playright p d b

  ------------------------------------------------------------------------------------------
 -- doms which will go left
 leftdrops :: Hand->DomBoard->Hand
 
 leftdrops h b = filter (\d -> goesLP d b) h
 
 -- doms which go right
 rightdrops :: Hand->DomBoard->Hand
 
 rightdrops h b = filter (\d -> goesRP d b) h 
 
 -------------------------------------------------
 -- 5s and 3s score for a number
  
 score53 :: Int->Int
 score53 n = 
  let 
   s3 = if (rem n 3)==0 then (quot n 3) else 0
   s5 = if (rem n 5)==0 then (quot n 5) else 0 
  in
   s3+s5
   
 ------------------------------------------------ 
 -- need comparing
 -- useful fn specifying what we want to compare by
 comparing :: Ord b=>(a->b)->a->a->Ordering
 comparing f l r = compare (f l) (f r)
 
 ------------------------------------------------
 -- scoreDom
 -- what will a given Dom score at a given end?
 -- assuming it goes
 
 scoreDom :: Dom->End->DomBoard->Int
 
 scoreDom d e b = scoreboard nb
                  where
                  (Just nb) = (playDom P1 d e b) -- player doesn't matter
 
 ----------------------------------------------------                 
 -- play to left - it will go
 playleft :: Player->Dom->DomBoard->DomBoard
 
 playleft p (d1,d2) InitBoard = Board (d1,d2) (d1,d2) [((d1,d2),p,1)]
 
 playleft p (d1,d2) (Board (l1,l2) r h)
  |d1==l1 = Board (d2,d1) r (((d2,d1),p,n+1):h)
  |otherwise =Board (d1,d2) r (((d1,d2),p,n+1):h)
  where
    n = maximum [m |(_,_,m)<-h] -- next drop number
    
 -- play to right
 playright :: Player->Dom->DomBoard->DomBoard
 
 playright p (d1,d2) InitBoard = Board (d1,d2) (d1,d2) [((d1,d2),p,1)]
 
 playright p (d1,d2)(Board l (r1,r2) h)
  |d1==r2 = Board l (d1,d2) (h++[((d1,d2),p,n+1)])
  |otherwise = Board l (d2,d1) (h++[((d2,d1),p,n+1)])
  where 
    n = maximum [m |(_,_,m)<-h] -- next drop number
 
 ------------------------------------------------------
 -- predicate - will given domino go at left?
 -- assumes a dom has been played
 
 goesLP :: Dom->DomBoard->Bool
 
 goesLP _ InitBoard = True
 
 goesLP (d1,d2) (Board (l,_) _ _) = (l==d1)||(l==d2)


 -- will dom go to the right?
 -- assumes a dom has been played
 
 goesRP :: Dom->DomBoard->Bool
 
 goesRP _ InitBoard = True
 
 goesRP (d1,d2) (Board _ (_,r) _) = (r==d1)||(r==d2)
 
 ------------------------------------------------

 -- playDom
 -- given player plays
 -- play a dom at left or right, if it will go

 
 playDom :: Player->Dom->End->DomBoard->Maybe DomBoard

 playDom p d L b
   |goesLP d b = Just (playleft p d b)
   |otherwise = Nothing
 
 playDom p d R b
   |goesRP d b = Just (playright p d b)
   |otherwise = Nothing
   
 ---------------------------------------------------    
 -- 5s & threes score for a board
 
 scoreboard :: DomBoard -> Int
 
 scoreboard InitBoard = 0

 scoreboard (Board (l1,l2) (r1,r2) hist)
  |length hist == 1 = score53 (l1+l2) -- 1 dom played, it's both left and right end
  |otherwise = score53 ((if l1==l2 then 2*l1 else l1)+ (if r1==r2 then 2*r2 else r2))   
 