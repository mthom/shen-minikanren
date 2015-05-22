(define test-equal
  [X | Xs] [Y | Ys] -> (test-equal Xs Ys) where (or (test-equal X Y) (mk-= X Y))
  [] [] -> true
  X Y -> (mk-= X Y)
  _ _ -> false)

(test-check "1.10"
  (run* Q
    mk-fail)
  [])

(test-check "1.11"
  (run* Q
    (=== true Q))
  [(wval true)])

(test-check "1.12"
  (run* Q
    mk-fail
    (=== true Q))
  [])

(test-check "1.13"
  (run* Q
    mk-succeed 
    (=== true Q))
  [(wval true)])

(test-check "1.14"
  (run* Q
    mk-succeed 
    (=== true Q))
  [(wval true)])

(test-check "1.15"
  (run* R 
    mk-succeed
    (=== corn R))
  [(wval corn)])

(test-check "1.16"
  (run* R 
    mk-succeed
    (=== corn R))
  [(wval corn)])

(test-check "1.17"
  (run* R
    mk-fail
    (=== corn R))
  [])

(test-check "1.18"
  (run* Q
    mk-succeed 
    (=== false Q))
  [(wval false)])

(test-check "1.22"
  (run* X
    (let X false
      (=== true X)))
  [])

(test-check "1.23"
  (run* Q
    (fresh (X)
      (=== true X)
      (=== true Q)))
   [(wval true)])

(test-check "1.26"
  (run* Q
    (fresh (X)
      (=== X true)
      (=== true Q)))
  [(wval true)])

(test-check "1.27"
  (run* Q
    (fresh (X)
      (=== X true)
      (=== Q true)))
  [(wval true)])

(test-check "1.28"
  (run* X mk-succeed)  
  [(create-var _.0)])

(test-check "1.29"
  (run* X
    (let X false
      (fresh (X)
	     (=== true X))))
  [(create-var _.0)])

(test-check "1.30"
  (run* R
    (fresh (X Y)
	   (=== [X Y] R)))
  [[(create-var _.0) (create-var _.1)]])

(test-check "1.31"
  (run* S
    (fresh (T U)
	   (=== [T U] S)))
  [[(create-var _.0) (create-var _.1)]])

(test-check "1.32"
  (run* R
    (fresh (X)
	   (let Y X
	     (fresh (X)
		    (=== [Y X Y] R)))))
  [[(create-var _.2) (create-var _.1) (create-var _.2)]])

(test-check "1.33"
  (run* R
    (fresh (X)
      (let Y X
        (fresh (X)
	       (=== [X Y X] R)))))
  [[(create-var _.2) (create-var _.1) (create-var _.2)]])

(test-check "1.34"
  (run* Q
    (=== false Q)
    (=== true Q))
  [])

(test-check "1.35"
  (run* Q
    (=== false Q)
    (=== false Q))
  [(wval false)])

(test-check "1.36"
  (run* Q
    (let X Q
      (=== true X)))
  [(wval true)])

(test-check "1.37"
  (run* R
    (fresh (X)
	   (=== X R)))
  [(create-var _.0)])

(test-check "1.38"
  (run* Q
    (fresh (X)
      (=== true X)
      (=== X Q)))
  [(wval true)])

(test-check "1.39"
  (run* Q
    (fresh (X)
      (=== X Q)
      (=== true X)))
  [(wval true)])

\* Note the use of wval below. *\
(test-check "1.40.1"
  (run* Q
    (fresh (X)
	   (=== (wval (= X Q)) Q)))
  [(wval false)])

(test-check "1.40.2"
  (run* Q
    (let X Q
      (fresh (Q)
	     (=== (wval (= X Q)) X))))
  [(wval false)])

(test-check "1.44"
  (run* Q
    (conde 
      (mk-fail mk-succeed) 
      (else mk-fail)))
  [])

(define null?
  { (list A) --> boolean }
  [] -> true
  _  -> false)

(test-check "1.45"
  (not (null? (run* Q
                (conde
                  (mk-fail mk-fail)
                  (else mk-succeed)))))
  true)

(test-check "1.46"
  (not (null? (run* Q
                (conde
                  (mk-succeed mk-succeed)
                  (else mk-fail)))))
  true)
  
(test-check "1.47"
  (run* X
    (conde
      ((=== olive X) mk-succeed)
      ((=== oil X) mk-succeed)
      (else mk-fail)))
  [(wval olive) (wval oil)])

(test-check "1.49"
  (run 1 X
    (conde
      ((=== olive X) mk-succeed)
      ((=== oil X) mk-succeed)
      (else mk-fail)))
  [(wval olive)])

(test-check "1.50.1"
  (run* X
    (conde
      ((=== virgin X) mk-fail)
      ((=== olive X) mk-succeed)
      (mk-succeed mk-succeed)
      ((=== oil X) mk-succeed)
      (else mk-fail)))
  [(wval olive) (create-var _.0) (wval oil)])

(test-check "1.50.2"
  (run* X
    (conde
      ((=== olive X) mk-succeed)
      (mk-succeed mk-succeed)
      ((=== oil X) mk-succeed)
      (else mk-fail)))
  [(wval olive) (create-var _.0) (wval oil)])

(test-check "1.52"
  (run 2 X
    (conde
      ((=== extra X) mk-succeed)
      ((=== virgin X) mk-fail)
      ((=== olive X) mk-succeed)
      ((=== oil X) mk-succeed)  
      (else mk-fail)))
  [(wval extra) (wval olive)])

(test-check "1.53"
  (run* R
	(fresh (X Y)
	       (=== split X)
	       (=== pea Y)
	       (=== [X Y] R)))
  [[(wval split) (wval pea)]])

(test-check "1.54"
  (run* R
    (fresh (X Y)
	   (conde
	    ((=== split X)	    
	     (=== pea Y))
	    ((=== navy X) (=== bean Y))
	    (else mk-fail))
	   (=== [X Y] R)))
  [[(wval split) (wval pea)] [(wval navy) (wval bean)]])

(test-check "1.55"
  (run* R
    (fresh (X Y)
      (conde
       ((=== split X) (=== pea Y))
       ((=== navy X) (=== bean Y))
       (else mk-fail))
      (=== [X Y soup] R)))
  [[(wval split) (wval pea) (wval soup)] [(wval navy) (wval bean) (wval soup)]])

(define teacupo
  { (walkable symbol) --> (query symbol) }
  X -> (conde ((=== tea X) mk-succeed)
	      ((=== cup X) mk-succeed)
	      (else mk-fail)))

(test-check "1.56"
  (run* X
    (teacupo X))
  [(wval tea) (wval cup)])

(test-check "1.57"
  (run* R
    (fresh (X Y)
      (conde
        ((teacupo X) (=== true Y) mk-succeed)
        ((=== false X) (=== true Y))
        (else mk-fail))
      (=== [X Y] R)))
  [[(wval tea) (wval true)] [(wval cup) (wval true)] [(wval false) (wval true)]])

(test-check "1.58"
  (run* R
    (fresh (X Y Z)
      (conde
        ((=== Y X) (fresh (X) (=== Z X)))
        ((fresh (X) (=== Y X)) (=== Z X))
        (else mk-fail))
      (=== [Y Z] R)))
  [[(create-var _.0) (create-var _.1)] [(create-var _.0) (create-var _.1)]])

(test-check "1.59"
  (run* R
    (fresh (X Y Z)
      (conde
	((=== Y X) (fresh (X) (=== Z X)))
	((fresh (X) (=== Y X)) (=== Z X))
	(else mk-fail))
      (=== false X)
      (=== [Y Z] R)))
  [[(wval false) (create-var _.0)] [(create-var _.0) (wval false)]])

(test-check "1.60"
  (run* Q
	(let A (=== true Q)
	     B (=== false Q)
	  B))
  [(wval false)])

(test-check "1.61"
  (run* Q
	(let A (=== true Q)
	     B (fresh (X)
		      (=== X Q)
		      (=== false X))
	     C (conde
		((=== true Q) mk-succeed)
		(else (=== false Q)))
	  B))
  [(wval false)])

(test-check "2.2"
  (run* R
	(fresh (X Y)
	       (=== [X Y] R)))
  [[(create-var _.0) (create-var _.1)]])

(test-check "2.3"
  (run* R
    (fresh (V W)
	   (=== (let X V Y W [X Y]) R)))
  [[(create-var _.0) (create-var _.1)]])

\* 2.9 *\
(define caro
  { (walkable A) --> (walkable A) --> (query A) } 
  P H -> (fresh (T) (=== [H | T] P)))

(test-check "2.6"
  (run* R (caro [a c o r n] R))
  [(wval a)])

(test-check "2.7"
  (run* Q
    (caro [a c o r n] a)
    (=== true Q))
  [(wval true)])

(test-check "2.8"
  (run* R
    (fresh (X Y)
      (caro [R Y] X)
      (=== [pear] X)))
  [[(wval pear)]])

(test-check "2.11"
  (run* R
    (fresh (X Y)
      (caro [grape raisin pair] X)
      (caro [[a] [b] [c]] Y)
      (=== [X | Y] R)))
  [[(wval grape) (wval a)]])

\* 2.16 *\
(define cdro
  { (walkable A) --> (walkable A) --> (query A) } 
  P T -> (fresh (H) (=== [H | T] P)))

(test-check "2.15"
  (run* R
    (fresh (V)
      (cdro [a c o r n] V)
      (caro V R)))
  [(wval c)])

(test-check "2.18"
  (run* R
    (fresh (X Y)
      (cdro [grape raisin pear] X)
      (caro [[a] [b] [c]] Y)
      (=== [X | Y] R)))
  [[[(wval raisin) (wval pear)] (wval a)]])

(test-check "2.19.1"
  (run* Q
	(cdro [a c o r n] [c o r n]) 
	(=== true Q))
  [(wval true)])

(test-check "2.20.1"
  (run* X
	(cdro [c o r n] [X r n]))
  [(wval o)])

(test-check "2.21"
  (run* L
    (fresh (X) 
      (cdro L [c o r n])
      (caro L X)
      (=== a X)))
  [[(wval a) (wval c) (wval o) (wval r) (wval n)]])

(define conso
  { (walkable A) --> (walkable A) --> (walkable A) --> (query A) } 
  H T P -> (=== [H | T] P))

(test-check "2.22"
  (run* L
	(conso [a b c] [d e] L))  
  [[[(wval a) (wval b) (wval c)] (wval d) (wval e)]])

(test-check "2.23.1"
  (run* X
    (conso X [a b c] [d a b c]))
  [(wval d)])

(test-check "2.24"
  (run* R
    (fresh (X Y Z)
      (=== [e a d X] R)
      (conso Y [a Z c] R)))
  [[e a d c]])

(test-check "2.25.1"
  (run* X (conso X [a X c] [d a X c]))
  [(wval d)])

(test-check "2.26"
  (run* L
    (fresh (X)
      (=== [d a X c] L)
      (conso X [a X c] L)))
  [[d a d c]])

(test-check "2.27"
  (run* L
    (fresh (X)
      (conso X [a X c] L)
      (=== [d a X c] L)))
  [[d a d c]])

(test-check "2.29"
  (run* L
    (fresh (D X Y W S)
      (conso W [a n s] S)
      (cdro L S)
      (caro L X)
      (=== b X)
      (cdro L D)
      (caro D Y)
      (=== e Y)))
  [[b e a n s]])

(define nullo
  { (walkable A) --> (query A) }
  X -> (=== [] X))

(test-check "2.32"
  (run* Q
    (nullo [grape raisin pear])
    (=== true Q))
  [])

(test-check "2.33"
  (run* Q
    (nullo [])
    (=== true Q))
  [(wval true)])

(test-check "2.34"
  (run* X
    (nullo X))
  [[]])

(define eqo
  { (walkable A) --> (walkable A) --> (query A) }
  X Y -> (=== X Y))

(test-check "2.38"
  (run* Q
    (eqo pear plum)
    (=== true Q))
  [])

(test-check "2.39"
  (run* Q
    (eqo plum plum)
    (=== true Q))
  [(wval true)])

(test-check "2.52"
  (run* R
    (fresh (X Y)
	   (=== [X Y salad] R)))
  [[(create-var _.0) (create-var _.1) (wval salad)]])

(define pairo
  { (walkable A) --> (query A) }
  P -> (fresh (A D) (conso A D P)))

(test-check "2.54"
  (run* Q
    (pairo [Q | Q])
    (=== true Q))
  [(wval true)])

(test-check "2.55"
  (run* Q
    (pairo [])
    (=== true Q))
  [])

(test-check "2.56"
  (run* Q
	(pairo pair)
	(=== true Q))
  [])

(test-check "2.57"
  (run* X (pairo X))
  [[(create-var _.0) | (create-var _.1)]])

(test-check "2.58"
  (run* R (pairo [R | pear]))
  [(create-var _.0)])

(define listo
  { (walkable A) --> (query A) }
  L -> (conde
	((nullo L) mk-succeed)
	((pairo L) (fresh (D)
			  (cdro L D)
			  (listo D)))
	(else mk-fail)))

(test-check "3.7"
  (run* X (listo [a b X d]))
  [(create-var _.0)])

(test-check "3.10"
  (run 1 X (listo [a b c | X]))
  [[]])

(test-check "3.14"
  (run 5 X (listo [a b c | X]))
  [[]
   [(create-var _.0)]
   [(create-var _.0) (create-var _.1)]
   [(create-var _.0) (create-var _.1) (create-var _.2)]
   [(create-var _.0) (create-var _.1) (create-var _.2) (create-var _.3)]])

(define list?
  [] -> true
  [_ | _] -> true
  _ -> false)

\* 3.16 *\
(define lol?
  [] -> true
  [H | T] -> (lol? T) where (list? H)
  _ -> true)

\* 3.17 *\ 
(define lolo
  { (walkable A) --> (query A) }
  L -> (conde
	((nullo L) mk-succeed)
	((fresh (A)
		(caro L A)
		(listo A))
	 (fresh (D)
		(cdro L D)
		(lolo D)))
	(else mk-fail)))

(test-check "3.20"
  (run 1 L
    (lolo L))
  [[]])

(test-check "3.21"
  (run* Q
    (fresh (X Y)
	   (lolo [[a b] [X c] [d Y]])
      (=== true Q)))
  [(wval true)])

(test-check "3.22"
  (run 1 Q
    (fresh (X)
	   (lolo [[a b] | X])
	   (=== true Q)))
  [(wval true)])

(test-check "3.23"
  (run 1 X
    (lolo [[a b] [c d] | X]))
  [[]])

(test-check "3.24"
  (run 5 X
    (lolo [[a b] [c d] | X]))
  [[]
   [[]]
   [[] []]
   [[] [] []]
   [[] [] [] []]])

\* 3.31 *\ 
(define twinso
  { (walkable A) --> (query A) }
  S -> (fresh (X Y)
	      (conso X Y S)
	      (conso X [] Y)))

(test-check "3.32"
  (run* Q
    (twinso [tofu tofu])
    (=== true Q))
  [(wval true)])

(test-check "3.33"
  (run* Z
    (twinso [Z tofu]))
  [(wval tofu)])

\* 3.36 *\
(define twinso
  { (walkable A) --> (query A) }
  S -> (fresh (X) (=== [X X] S)))

\* 3.37 *\
(define loto
  { (walkable A) --> (query A) }
  L -> (conde
	((nullo L) mk-succeed)
	((fresh (A)
		(caro L A)
		(twinso A))
	 (fresh (D)
		(cdro L D)
		(loto D)))
	(else mk-fail)))

(test-check "3.38"
  (run 1 Z
    (loto [[g g] | Z]))
  [[]])

(test-check "3.42"
  (run 5 Z (loto [[g g] | Z]))
  [[]   
   [[(create-var _.1) (create-var _.1)]]
   [[(create-var _.1) (create-var _.1)] [(create-var _.3) (create-var _.3)]]
   [[(create-var _.1) (create-var _.1)] [(create-var _.3) (create-var _.3)] [(create-var _.5) (create-var _.5)]]
   [[(create-var _.1) (create-var _.1)] [(create-var _.3) (create-var _.3)] [(create-var _.5) (create-var _.5)]
    [(create-var _.7) (create-var _.7)]]])

(test-check "3.45"
  (run 5 R
    (fresh (W X Y Z)
      (loto [[g g] [e W] [X Y] | Z])
      (=== [W [X Y] Z] R)))
  [[e [(create-var _.1) (create-var _.1)] []]
   [e [(create-var _.1) (create-var _.1)] [[(create-var _.3) (create-var _.3)]]]
   [e [(create-var _.1) (create-var _.1)] [[(create-var _.3) (create-var _.3)] [(create-var _.5) (create-var _.5)]]]
   [e [(create-var _.1) (create-var _.1)] [[(create-var _.3) (create-var _.3)] [(create-var _.5) (create-var _.5)]
					   [(create-var _.7) (create-var _.7)]]]
   [e [(create-var _.1) (create-var _.1)] [[(create-var _.3) (create-var _.3)] [(create-var _.5) (create-var _.5)]
			       [(create-var _.7) (create-var _.7)] [(create-var _.9) (create-var _.9)]]]])

(test-check "3.47"
  (run 3 Out
    (fresh (W X Y Z)
      (=== [[g g] [e W] [X Y] | Z] Out)
      (loto Out)))
  [[[g g] [e e] [(create-var _.1) (create-var _.1)]]
   [[g g] [e e] [(create-var _.1) (create-var _.1)] [(create-var _.3) (create-var _.3)]]
   [[g g] [e e] [(create-var _.1) (create-var _.1)] [(create-var _.3) (create-var _.3)] [(create-var _.5) (create-var _.5)]]])

\* 3.48 *\
(define listofo
  { ((walkable A) --> (query A)) --> (walkable A) --> (query A) }
  Predo L -> (conde ((nullo L) mk-succeed)
		    ((fresh (A)
			    (caro L A)
			    (Predo A))
		     (fresh (D)
			    (cdro L D)
			    (listofo Predo D)))
		    (else mk-fail)))

(test-check "3.49"
  (run 3 Out
    (fresh (W X Y Z)
      (=== [[g g] [e W] [X Y] | Z] Out)
      (listofo (wguard twinso) Out)))
  [[[g g] [e e] [(create-var _.1) (create-var _.1)]]
   [[g g] [e e] [(create-var _.1) (create-var _.1)]
    [(create-var _.3) (create-var _.3)]]
   [[g g] [e e] [(create-var _.1) (create-var _.1)]
    [(create-var _.3) (create-var _.3)] [(create-var _.5) (create-var _.5)]]])

\* 3.50 *\
(define loto
  { (walkable A) --> (query A) }
  L -> (listofo twinso L))

\* 3.51.2 *\
(define eq-car?
  { (walkable A) --> (walkable A) --> boolean }
  [X | _] X -> true
  _ _ -> false)

\* 3.54.1 *\
(define eq-caro
  { (walkable A) --> (walkable A) --> (query A) }
  L X -> (caro L X))

\* 3.54.2 *\
(define membero
  { (walkable A) --> (walkable A) --> (query A) }
  X L -> (conde ((nullo L) mk-fail)
		((eq-caro L X) mk-succeed)
		(else (fresh (D)
			     (cdro L D)
			     (membero X D)))))

(test-check "3.57"
  (run* Q
    (membero olive [virgin olive oil])
    (=== true Q))
  [(wval true)])

(test-check "3.58"
  (run 1 Y
    (membero Y [hummus with pita]))
  [(wval hummus)])

(test-check "3.59"
  (run 1 Y
    (membero Y [with pita]))
  [(wval with)])

(test-check "3.60"
  (run 1 Y (membero Y [pita]))
  [(wval pita)])

(test-check "3.61"
  (run* Y (membero Y []))
  [])

(test-check "3.62"
  (run* Y (membero Y [hummus with pita]))
  (map wval [hummus with pita]))

\* 3.65 *\ 
(define identity
  { (walkable A) --> (list (walkable A)) }
  L -> (run* Y (membero Y L)))

(test-check "3.66"
  (run* X (membero e [pasta X fagioli]))
  [(wval e)])

(test-check "3.69"
  (run 1 X (membero e [pasta e X fagioli]))
  [(create-var _.0)])

(test-check "3.70"
  (run 1 X (membero e [pasta X e fagioli]))
  [(wval e)])

(test-check "3.71"
  (run* R
    (fresh (X Y)
      (membero e [pasta X fagioli Y])
      (=== [X Y] R)))
  [[e (create-var _.0)] [(create-var _.0) e]])

(test-check "3.73"
	    (run 1 L (membero tofu L))
	    [[tofu | (create-var _.0)]])

(test-check "3.76"
	    (run 5 L (membero tofu L))
	    [[tofu | (create-var _.0)]
	     [(create-var _.0) tofu | (create-var _.1)]
	     [(create-var _.0) (create-var _.1) tofu | (create-var _.2)]
	     [(create-var _.0) (create-var _.1) (create-var _.2) tofu | (create-var _.3)]
	     [(create-var _.0) (create-var _.1) (create-var _.2) (create-var _.3) tofu | (create-var _.4)]])

\* 3.80.1 *\ 
(define pmembero
  { (walkable A) --> (walkable A) --> (query A) }
  X L -> (conde ((nullo L) mk-fail)
		((eq-caro L X) (cdro L []))
		(else (fresh (D)
			     (cdro L D)
			     (pmembero X D)))))

(test-check "3.80.2"
	    (run 5 L (pmembero tofu L))
	    [[(wval tofu)]
	     [(create-var _.0) tofu]
	     [(create-var _.0) (create-var _.1) tofu]
	     [(create-var _.0) (create-var _.1) (create-var _.2) tofu]
	     [(create-var _.0) (create-var _.1) (create-var _.2) (create-var _.3) tofu]])

(test-check "3.81"
  (run* Q
    (pmembero tofu [a b tofu d tofu])
    (=== true Q))
  [(wval true)])

\* 3.83 *\ 
(define pmembero
  { (walkable A) --> (walkable A) --> (query A) }
  X L -> (conde ((nullo L) mk-fail)
		((eq-caro L X) (cdro L []))
		((eq-caro L X) mk-succeed)
		(else (fresh (D)
			     (cdro L D)
			     (pmembero X D)))))

(test-check "3.84"
  (run* Q
    (pmembero tofu [a b tofu d tofu])
    (=== true Q))
  [(wval true) (wval true) (wval true)])

\* 3.86 *\ 
(define pmembero
  { (walkable A) --> (walkable A) --> (query A) }
  X L -> (conde ((nullo L) mk-fail)
		((eq-caro L X) (cdro L []))
		((eq-caro L X) (fresh (A D)
				      (cdro L [A | D])))
		(else (fresh (D)
			     (cdro L D)
			     (pmembero X D)))))

(test-check "3.88"
  (run* Q
    (pmembero tofu [a b tofu d tofu])
    (=== (wval true) Q))
  [(wval true) (wval true)])

\* 3.93 *\
(define pmembero
  { (walkable A) --> (walkable A) --> (query A) }
  X L -> (conde
	  ((eq-caro L X) (fresh (A D)
				(cdro L [A | D])))
	  ((eq-caro L X) (cdro L []))
	  (else (fresh (D)
		       (cdro L D)
		       (pmembero X D)))))

\* 3.95 *\
(define first-value
  { (walkable A) --> (list (walkable A)) }
  L -> (run 1 Y (membero Y L)))

(test-check "3.96"
	    (first-value [pasta e fagioli])
	    [pasta])

\* 3.98 *\
(define memberrevo
  { (walkable A) --> (walkable A) --> (query A) }
  X L -> (conde ((nullo L) mk-fail)
		(mk-succeed (fresh (D)
				   (cdro L D)
				   (memberrevo X D)))
		(else (eq-caro L X))))

(test-check "3.100"
  (run* X (memberrevo X [pasta e fagioli]))
  [fagioli e pasta])

\* 3.101 *\
(define reverse-list
  L -> (run* Y (memberrevo Y L)))

\* 4.1.1 *\
(define mem
  X [] -> false
  X [X | L] -> [X | L]
  X [_ | L] -> (mem X L))    

(test-check "4.1.2"
	    (mem tofu [a b tofu d peas e])
	    [tofu d peas e])

(test-check "4.3"
  (run* Out
	(=== (mem tofu [a b tofu d peas e]) Out))
  [(map wval [tofu d peas e])])

\* 4.7 *\
(define memo
  X L Out -> (conde ((nullo L) mk-fail)
		    ((eq-caro L X) (=== L Out))
		    (else (fresh (D)
				 (cdro L D)
				 (memo X D Out)))))

(test-check "4.10"
  (run 1 Out (memo tofu [a b tofu d tofu e] Out))
  [[tofu d tofu e]])

(test-check "4.11"
  (run 1 Out 
    (fresh (X)
	   (memo tofu [a b X d tofu e] Out)))
  [[tofu d tofu e]])

(test-check "4.12"
  (run* R
    (memo R [a b tofu d tofu e] [tofu d tofu e]))
  [tofu])

(test-check "4.13"
  (run* Q
    (memo tofu [tofu e] [tofu e])
    (=== true Q))
  [true])

(test-check "4.14"
  (run* Q
    (memo tofu [tofu e] [tofu])
    (=== true Q))
  [])

(test-check "4.15"
  (run* X
    (memo tofu [tofu e] [X e]))
  [tofu])

(test-check "4.16"
  (run* X
    (memo tofu [tofu e] [peas X]))
  [])

(test-check "4.17"
  (run* Out
    (fresh (X) 
      (memo tofu [a b X d tofu e] Out)))
  [[tofu d tofu e] [tofu e]])

(test-check "4.18"
  (run 12 Z
    (fresh (U)
	   (memo tofu [a b tofu d tofu e | Z] U)))  
  [(create-var _.0)
   (create-var _.0)
   [tofu | (create-var _.0)]
   [(create-var _.0) tofu | (create-var _.1)]
   [(create-var _.0) (create-var _.1) tofu | (create-var _.2)]
   [(create-var _.0) (create-var _.1) (create-var _.2) tofu | (create-var _.3)]
   [(create-var _.0) (create-var _.1) (create-var _.2) (create-var _.3) tofu | (create-var _.4)]
   [(create-var _.0) (create-var _.1) (create-var _.2) (create-var _.3) (create-var _.4) tofu | (create-var _.5)]
   [(create-var _.0) (create-var _.1) (create-var _.2) (create-var _.3) (create-var _.4) (create-var _.5) tofu | (create-var _.6)]
   [(create-var _.0) (create-var _.1) (create-var _.2) (create-var _.3) (create-var _.4) (create-var _.5) (create-var _.6) tofu | (create-var _.7)]
   [(create-var _.0) (create-var _.1) (create-var _.2) (create-var _.3) (create-var _.4) (create-var _.5) (create-var _.6) (create-var _.7) tofu | (create-var _.8)]
   [(create-var _.0) (create-var _.1) (create-var _.2) (create-var _.3) (create-var _.4) (create-var _.5) (create-var _.6) (create-var _.7) (create-var _.8) tofu | (create-var _.9)]])

\* 4.21 *\
(define memo
  { (walkable A) --> (walkable A) --> (walkable A) --> (query A) }
  X L Out -> (conde ((eq-caro L X) (=== L Out))
		    (else (fresh (D)
				 (cdro L D)
				 (memo X D Out)))))

\* 4.22 *\
(define rember
  X L -> (cases (null? L) []
		(eq-car? L X) (tail L)
		true [(head L) | (rember X (tail L))]))

(test-check "4.23"
	    (rember peas [a b peas d peas e])
	    [a b d peas e])

\* 5.59 *\ 
(define flatteno
  S Out -> (conde
	    ((nullo S) (=== [] Out))
	    ((pairo S)
	     (fresh (A D Res-a Res-d)
		    (conso A D S)
		    (flatteno A Res-a)
		    (flatteno D Res-d)
		    (appendo Res-a Res-d Out)))
	    (else (conso S [] Out))))

(test-check "5.60"
  (run 1 X
    (flatteno [[a b] c] X))
  [[a b c]])

\* 7.5 *\
(define bit-xoro
  X Y R -> (conde
      ((=== 0 X) (=== 0 Y) (=== 0 R))
      ((=== 1 X) (=== 0 Y) (=== 1 R))
      ((=== 0 X) (=== 1 Y) (=== 1 R))
      ((=== 1 X) (=== 1 Y) (=== 0 R))
      (else mk-fail)))

(test-check "7.6"
	    (run* S
		  (fresh (X Y)
			 (bit-xoro X Y 0)
			 (=== [X Y] S)))
	    [[0 0] [1 1]])

(test-check "7.97"
  (run 3 S
    (fresh (X Y R)
      (addero 0 X Y R)
      (=== [X Y R] S)))
  [[(create-var _.1) [] (create-var _.1)]
   [[] [(create-var _.2) | (create-var _.3)] [(create-var _.2) | (create-var _.3)]]
   [[1] [1] [0 | 1]]])

(test-check "8.4"
  (run* P
    (*o [0 1] [0 0 1] P))  
  [[0 0 0 1]])

(test-check "10.14"
  (run* Q
    (condu
      ((alwayso) mk-succeed)
      (else mk-fail))
    (=== true Q))
  [true])

(test-check "10.18"
  (run 1 Q
    (condu
      ((alwayso) mk-succeed)
      (else mk-fail))
    mk-fail
    (=== true Q))
  [])

(define onceo
  G -> (condu
	(G mk-succeed)
	(else mk-fail)))

(test-check "10.19.2"
  (run* X
    (onceo (teacupo X)))
  [tea])

(test-check "10.22"
	    (run* R		  
    (conda
     ((teacupo R) mk-succeed)
     ((=== false R) mk-succeed)
     (else mk-fail)))
  [tea cup])

(test-check "10.23"
  (run* R
    (=== false R)
    (conda
      ((teacupo R) mk-succeed)
      ((=== false R) mk-succeed)
      (else mk-fail)))
  [false])

(test-check "10.24"
	    (run* R
		  (=== false R)
		  (condu
		   ((teacupo R) mk-succeed)
		   ((=== false R) mk-succeed)
		   (else mk-fail)))
	    [false])
