data Lam2Expr = DeBruijn Int | Lambda Lam2Expr | App Lam2Expr Lam2Expr | Unknown | LamOrApp | UnknownDeBruijn Int
instance Show Lam2Expr where
         show l = case l of DeBruijn n -> show n
                            Lambda lx -> "λ"++show lx
                            App lx ly -> "("++show lx++")"++"("++show ly++")"
                            Unknown -> "x"
                            LamOrApp -> "#"
                            UnknownDeBruijn n -> show n++"?"

loop = loop
splitTermData cs = let depth ccs i = case ccs of '!':[] -> i:[]
                                                 '0':'0':cccs -> i:i:depth cccs i
                                                 '0':'1':cccs -> i:i:depth cccs (i+1)
                                                 '0':'!':[] -> i:i:[]
                                                 '1':'1':cccs -> i:depth ('1':cccs) i 
                                                 '1':'0':cccs -> i:i:depth cccs (i-1)
                                                 '1':'!':[] -> i:i:[] 
                                                 [] -> [] in (map snd.takeWhile ((/=(-1)).fst).zip (depth cs 0)$cs, map snd.dropWhile ((/=(-1)).fst).zip (depth cs 0)$cs)

parseDeBruijn s i = case s of '0':[] -> DeBruijn i
                              '!':[] -> UnknownDeBruijn i
                              '1':cs -> parseDeBruijn cs (i+1)

parsebbl2 s = let parseTerm cs = case cs of '!':[] -> Unknown
                                            '0':'0':ccs -> Lambda (parseTerm ccs)
                                            '0':'!':[] -> LamOrApp
                                            '1':ccs -> parseDeBruijn ('1':ccs) 0
                                            '0':'1':ccs -> case splitTermData ccs of (cccs, "") -> App (parseTerm cccs) Unknown
                                                                                     (ccxs, ccys) -> App (parseTerm ccxs) (parseTerm ccys) in case splitTermData s of (cxs, cys) -> (parseTerm cxs, cys)

data Trool = TRUE | MAYBE | FALSE
     deriving (Show)

andTrool p q = case (p, q) of (FALSE, _) -> FALSE
                              (_, FALSE) -> FALSE
                              (MAYBE, _) -> MAYBE
                              (_, MAYBE) -> MAYBE
                              (TRUE, _) -> TRUE
                              (_, TRUE) -> TRUE

orTrool p q = case (p, q) of (TRUE, _) -> TRUE
                             (_, TRUE) -> TRUE
                             (MAYBE, _) -> MAYBE
                             (_, MAYBE) -> MAYBE
                             (FALSE, _) -> FALSE
                             (_, FALSE) -> FALSE

notTrool p = case p of TRUE -> FALSE
                       MAYBE -> MAYBE
                       FALSE -> TRUE

combineTrool p q = case (p, q) of (MAYBE, x) -> x
                                  (x, MAYBE) -> x
                                  (TRUE, TRUE) -> TRUE
                                  (FALSE, FALSE) -> FALSE

toTrool p = case p of True -> TRUE
                      False -> FALSE

--what it SHOULD do: return FALSE if l has any free vars in it, TRUE if it definitely has no free vars, and MAYBE otherwise
syntaxValid (l, s) = let syntaxParse l i = case l of Unknown -> MAYBE
                                                     LamOrApp -> MAYBE
                                                     Lambda lx -> syntaxParse lx (i+1)
                                                     DeBruijn j -> if (i>=j) then TRUE else FALSE
                                                     UnknownDeBruijn j -> if (i>=j) then MAYBE else FALSE
                                                     App lx ly -> andTrool (syntaxParse lx i) (syntaxParse ly i) in syntaxParse l 0

--what it SHOULD do: return FALSE if l has any free vars in it, and MAYBE otherwise
syntaxDecider s = andTrool MAYBE (syntaxValid s)

isNormal l = case l of Unknown -> MAYBE
                       LamOrApp -> MAYBE
                       Lambda lx -> isNormal lx
                       DeBruijn i -> TRUE
                       UnknownDeBruijn i -> TRUE
                       App (Lambda lx) ly -> FALSE
                       App lx ly -> andTrool (isNormal lx) (isNormal ly)

--what it SHOULD do: return FALSE if l isn't in normal form, has any free vars, or doesn't discard the data, MAYBE if l is incomplete, and TRUE if l is complete, in normal form and discards the data 
discardDataAndIsNormal (l, s) = case l of Lambda lx -> andTrool (isNormal l) (syntaxValid (lx, "!"))
                                          lx -> FALSE

--what it SHOULD do: return TRUE if l is complete, in normal form, and discards the data, and MAYBE otherwise
discardDataAndIsNormalDecider s = orTrool MAYBE (discardDataAndIsNormal s)

--what it SHOULD do: check if the ith free variable is head-reduced
headReducesInput l i = case l of Unknown -> MAYBE
                                 LamOrApp -> MAYBE
                                 Lambda lx -> headReducesInput lx (i+1)
                                 DeBruijn j -> if (i==j) then TRUE else FALSE
                                 UnknownDeBruijn j -> if (i>=j) then MAYBE else FALSE
                                 App (Lambda lx) ly -> MAYBE
                                 App lx ly -> headReducesInput lx i

--what it SHOULD do: return TRUE if l is in normal form and has a copy of the ith free variable where nothing is applied to it, MAYBE if l is not in normal form or incomplete, and FALSE otherwise
hasNonHeadReducedInput l i = case l of Unknown -> MAYBE
                                       LamOrApp -> MAYBE
                                       Lambda lx -> hasNonHeadReducedInput lx (i+1)
                                       DeBruijn j -> if (i==j) then TRUE else FALSE
                                       UnknownDeBruijn j -> if (i>=j) then MAYBE else FALSE
                                       App (Lambda lx) ly -> MAYBE
                                       App lx ly -> andTrool (notTrool (headReducesInput lx i)) (orTrool (hasNonHeadReducedInput lx i) (hasNonHeadReducedInput ly i))

--what it SHOULD do: return FALSE if l has free vars or l is in normal form and has a copy of the data where nothing is applied to it, and MAYBE otherwise
readsAndHasNonAppliedToDataDecider (l, s) = case syntaxValid (l, s) of FALSE -> FALSE
                                                                       _ -> andTrool MAYBE (notTrool (hasNonHeadReducedInput l 0))

data OmegaTree = Leaf [Char] Trool | Branch OmegaTree OmegaTree
instance Show OmegaTree where
         show o = case o of Leaf cs TRUE -> cs++" Halt"
                            Leaf cs MAYBE -> cs++" Split"
                            Leaf cs FALSE -> cs++" Impossible"
                            Branch ox oy -> "("++show ox++", "++show oy++")"

decider s = foldr ($ s) MAYBE (map (combineTrool.) [syntaxDecider, discardDataAndIsNormalDecider, readsAndHasNonAppliedToDataDecider])

omegaTree i s = case i of 0 -> Leaf s MAYBE
                          n -> case decider (parsebbl2 s) of FALSE -> Leaf s FALSE 
                                                             MAYBE -> Branch (omegaTree (n-1) (init s++"0!")) (omegaTree (n-1) (init s++"1!"))
                                                             TRUE -> Leaf s TRUE

pairAvg p1 p2 = case p1 of (x1, x2) -> case p2 of (y1, y2) -> ((x1+y1)/2, (x2+y2)/2)

omegaBound :: OmegaTree -> (Rational, Rational)
omegaBound t = case t of Leaf cs TRUE -> (1, 1)
                         Leaf cs MAYBE -> (0, 1)
                         Leaf cs FALSE -> (0, 0)
                         Branch tx ty -> pairAvg (omegaBound tx) (omegaBound ty)

main = print.omegaBound.omegaTree 24$"!"
