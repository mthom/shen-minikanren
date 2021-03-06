(define replace
     X XG [X | Xs] -> [XG | (replace X XG Xs)]
     X XG [L | Ls] -> [(replace X XG L) | (replace X XG Ls)]
     X XG [] -> []
     X XG X  -> XG
     _ _  L  -> L)

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
	       [lambdag@ S [G S]])
  [all G | Gs] -> (let S (gensym (protect S))
		    [lambdag@ S [mk-bind [G S] [all | Gs]]]))

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
