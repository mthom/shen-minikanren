(defmacro incf-macro
  [incf Loc]     -> [incf Loc 0]
  [incf Loc Def] -> (let N (gensym (protect N))
		      [let N [trap-error [value Loc] [/. _ [set Loc Def]]]
			[set Loc [+ N 1]]]))

(define replace
  X XG [X | Xs] -> [XG | (replace X XG Xs)]
  X XG [L | Ls] -> [(replace X XG L) | (replace X XG Ls)]
  X XG [] -> []
  X XG X  -> XG
  _ _  L  -> L)

(define inject-values
  [] -> []
  [wguard X] -> X
  [wval X] -> [wval X]
  [X | Xs] -> [X | (map inject-values Xs)] where (cons? Xs)
  [X | Y] -> [(inject-values X) | (inject-values Y)]
  V -> V where (variable? V)
  mk-succeed -> mk-succeed
  mk-fail -> mk-fail
  X -> [wval X])

(defmacro mzero-macro
  [mzero] -> [])

(defmacro unit-macro
  [unit A] -> A)

(synonyms (pairs A) (list (substitution (walkable A))))

(defmacro size-s-macro
  [size-s Ls] -> [length Ls])  

(defmacro lambdag@-macro
  [lambdag@ S E] -> [/. S E])

(defmacro lambdaf@-macro
  [lambdaf@ E] -> [freeze E])

(defmacro fresh-macro
  [fresh [X | Xs] G | Gs] -> (let S (gensym (protect S))
			       [lambdag@ S [fresh-term S [X | Xs] G | Gs]]))

(defmacro fresh-term-macro
  [fresh-term S [] G | Gs] -> [[all G | Gs] S]
  [fresh-term S [X | Xs] G | Gs] -> (let XG (gensym (protect X))
				      (replace X XG
					     [[/. XG
						  [fresh-term S Xs G | Gs]]
					      [create-var [protect XG]]]))
  where (variable? X))

(defmacro run-macro
  [run nothing X G | Gs] -> (let S  (gensym (protect S))
			         XG (gensym (protect X))
			      (replace X XG 
				     [[/. XG 
					  [map-inf nothing
						   [/. S [reify [walk* X S]]]
						   [[all G | Gs] [empty-s]]]]
				      [create-var [protect XG]]]))
  [run NHat X G | Gs] -> (let S  (gensym (protect S))
			      XG (gensym (protect X))
			   (replace X XG
				  [[/. XG
				       [map-inf [cons just [cons NHat []]]
						[/. S [reify [walk* X S]]]
						[[all G | Gs] [empty-s]]]]
				   [create-var [protect XG]]]))
  where (and (number? NHat) (> NHat 0)))

(defmacro all-macro
  [all]   -> [mk-succeed]
  [all G] -> (let S (gensym (protect S))
	          GV (inject-values G)
	       [lambdag@ S [GV S]])
  [all G | Gs] -> (let S (gensym (protect S))
		       GV (inject-values G)
		    [lambdag@ S [mk-bind [GV S] [all | Gs]]]))

(defmacro run*-macro
  [run* X G | Gs] -> [run nothing X G | Gs])

(defmacro test-check-macro
  [test-check Title Expr Result] -> (let Expected (gensym (protect E))
				         Produced (gensym (protect P))
				      [do
				       [print [@s "Testing " [str Title]]]
				       [let Expected Result
					    Produced Expr
					 [or [test-equal Expected Produced]
					     [error "test-check failed"]]]]))
