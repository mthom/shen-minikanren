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
  [true])

(test-check "1.12"
  (run* Q
    mk-fail
    (=== true Q))
  [])

(test-check "1.13"
  (run* Q
    mk-succeed 
    (=== true Q))
  [true])

(test-check "1.14"
  (run* Q
    mk-succeed 
    (=== true Q))
  [true])

(test-check "1.15"
  (run* R 
    mk-succeed
    (=== corn R))
  [corn])

(test-check "1.16"
  (run* R 
    mk-succeed
    (=== corn R))
  [corn])

(test-check "1.17"
  (run* R
    mk-fail
    (=== corn R))
  [])

(test-check "1.18"
  (run* Q
    mk-succeed 
    (=== false Q))
  [false])

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
   [true])

(test-check "1.26"
  (run* Q
    (fresh (X)
      (=== X true)
      (=== true Q)))
  [true])

(test-check "1.27"
  (run* Q
    (fresh (X)
      (=== X true)
      (=== Q true)))
  [true])

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
  [false])

(test-check "1.36"
  (run* Q
    (let X Q
      (=== true X)))
  [true])

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
  [true])

(test-check "1.39"
  (run* Q
    (fresh (X)
      (=== X Q)
      (=== true X)))
  [true])

(test-check "1.40.1"
  (run* Q
    (fresh (X)
	   (=== (= X Q) Q)))
  [false])

(test-check "1.40.2"
  (run* Q
    (let X Q
      (fresh (Q)
	     (=== (= X Q) X))))
  [false])

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
  [olive oil])

(test-check "1.49"
  (run 1 X
    (conde
      ((=== olive X) mk-succeed)
      ((=== oil X) mk-succeed)
      (else mk-fail)))
  [olive])

(test-check "1.50.1"
  (run* X
    (conde
      ((=== virgin X) mk-fail)
      ((=== olive X) mk-succeed)
      (mk-succeed mk-succeed)
      ((=== oil X) mk-succeed)
      (else mk-fail)))
  [olive (create-var _.0) oil])

(test-check "1.50.2"
  (run* X
    (conde
      ((=== olive X) mk-succeed)
      (mk-succeed mk-succeed)
      ((=== oil X) mk-succeed)
      (else mk-fail)))
  [olive (create-var _.0) oil])

(test-check "1.52"
  (run 2 X
    (conde
      ((=== extra X) mk-succeed)
      ((=== virgin X) mk-fail)
      ((=== olive X) mk-succeed)
      ((=== oil X) mk-succeed)  
      (else mk-fail)))
  [extra olive])

(test-check "1.53"
  (run* R
	(fresh (X Y)
	       (=== split X)
	       (=== pea Y)
	       (=== [X Y] R)))
  [[split pea]])

(test-check "1.54"
  (run* R
    (fresh (X Y)
	   (conde
	    ((=== split X)	    
	     (=== pea Y))
	    ((=== navy X) (=== bean Y))
	    (else mk-fail))
	   (=== [X Y] R)))
  [[split pea] [navy bean]])

(test-check "1.55"
  (run* R
    (fresh (X Y)
      (conde
       ((=== split X) (=== pea Y))
       ((=== navy X) (=== bean Y))
       (else mk-fail))
      (=== [X Y soup] R)))
  [[split pea soup] [navy bean soup]])

(define teacupo
  { (walkable symbol) --> (query symbol) }
  X -> (conde ((=== tea X) mk-succeed)
	      ((=== cup X) mk-succeed)
	      (else mk-fail)))

(test-check "1.56"
  (run* X
    (teacupo X))
  [tea cup])

(test-check "1.57"
  (run* R
    (fresh (X Y)
      (conde
        ((teacupo X) (=== true Y) mk-succeed)
        ((=== false X) (=== true Y))
        (else mk-fail))
      (=== [X Y] R)))
  [[tea true] [cup true] [false true]])

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
  [[false (create-var _.0)] [(create-var _.0) false]])

(test-check "1.60"
  (run* Q
	(let A (=== true Q)
	     B (=== false Q)
	  B))
  [false])

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
  [false])

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
  [a])

(test-check "2.7"
  (run* Q
    (caro [a c o r n] a)
    (=== true Q))
  [true])

(test-check "2.8"
  (run* R
    (fresh (X Y)
      (caro [R Y] X)
      (=== [pear] X)))
  [[pear]])

(test-check "2.11"
  (run* R
    (fresh (X Y)
      (caro [grape raisin pair] X)
      (caro [[a] [b] [c]] Y)
      (=== [X | Y] R)))
  [[grape a]])

\* 2.16 *\
(define cdro
  { (walkable A) --> (walkable A) --> (query A) } 
  P T -> (fresh (H) (=== [H | T] P)))

(test-check "2.15"
  (run* R
    (fresh (V)
      (cdro [a c o r n] V)
      (caro V R)))
  [c])

(test-check "2.18"
  (run* R
    (fresh (X Y)
      (cdro [grape raisin pear] X)
      (caro [[a] [b] [c]] Y)
      (=== [X | Y] R)))
  [[[raisin pear] a]])

(test-check "2.19.1"
  (run* Q
	(cdro [a c o r n] [c o r n]) 
	(=== true Q))
  [true])

(test-check "2.20.1"
  (run* X
	(cdro [c o r n] [X r n]))
  [o])

(test-check "2.21"
  (run* L
    (fresh (X) 
      (cdro L [c o r n])
      (caro L X)
      (=== a X)))
  [[a c o r n]])

(define conso
  { (walkable A) --> (walkable A) --> (walkable A) --> (query A) } 
  H T P -> (=== [H | T] P))

(test-check "2.22"
  (run* L
	(conso [a b c] [d e] L))  
  [[[a b c] d e]])

(test-check "2.23.1"
  (run* X
    (conso X [a b c] [d a b c]))
  [d])

(test-check "2.24"
  (run* R
    (fresh (X Y Z)
      (=== [e a d X] R)
      (conso Y [a Z c] R)))
  [[e a d c]])

(test-check "2.25.1"
  (run* X (conso X [a X c] [d a X c]))
  [d])

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
  [true])

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
  [true])

(test-check "2.52"
  (run* R
    (fresh (X Y)
	   (=== [X Y salad] R)))
  [[(create-var _.0) (create-var _.1) salad]])

(define pairo
  { (walkable A) --> (query A) }
  P -> (fresh (A D) (conso A D P)))

(test-check "2.54"
  (run* Q
    (pairo [Q | Q])
    (=== true Q))
  [true])

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
  [true])

(test-check "3.22"
  (run 1 Q
    (fresh (X)
	   (lolo [[a b] | X])
	   (=== true Q)))
  [true])

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
  [true])

(test-check "3.33"
  (run* Z
    (twinso [Z tofu]))
  [tofu])

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
      (listofo twinso Out)))
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
  { (list (walkable A)) --> (walkable A) --> boolean }
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
  [true])

(test-check "3.58"
  (run 1 Y
    (membero Y [hummus with pita]))
  [hummus])

(test-check "3.59"
  (run 1 Y
    (membero Y [with pita]))
  [with])

(test-check "3.60"
  (run 1 Y (membero Y [pita]))
  [pita])

(test-check "3.61"
  (run* Y (membero Y []))
  [])

(test-check "3.62"
  (run* Y (membero Y [hummus with pita]))
  [hummus with pita])

\* 3.65 *\ 
(define identity
  { (walkable A) --> (list (walkable A)) }
  L -> (run* Y (membero Y L)))

(test-check "3.66"
  (run* X (membero e [pasta X fagioli]))
  [e])

(test-check "3.69"
  (run 1 X (membero e [pasta e X fagioli]))
  [(create-var _.0)])

(test-check "3.70"
  (run 1 X (membero e [pasta X e fagioli]))
  [e])

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
	    [[tofu]
	     [(create-var _.0) tofu]
	     [(create-var _.0) (create-var _.1) tofu]
	     [(create-var _.0) (create-var _.1) (create-var _.2) tofu]
	     [(create-var _.0) (create-var _.1) (create-var _.2) (create-var _.3) tofu]])

(test-check "3.81"
  (run* Q
    (pmembero tofu [a b tofu d tofu])
    (=== true Q))
  [true])

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
  [true true true])

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
    (=== true Q))
  [true true])

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
  { (walkable A) --> (list (walkable A)) }
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
  [[tofu d peas e]])

\* 4.7 *\
(define memo
  { (walkable A) --> (walkable A) --> (walkable A) --> (query A) }
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
  { (walkable A) --> (list (walkable A)) --> (list (walkable A)) }  
  X L -> (cases (null? L) []
		(eq-car? L X) (tail L)
		true [(head L) | (rember X (tail L))]))

(test-check "4.23"
	    (rember peas [a b peas d peas e])
	    [a b d peas e])

\* 4.27 *\ 
(define rembero
  { (walkable A) --> (walkable A) --> (walkable A) --> (query A) }  
  X L Out -> (conde
	      ((nullo L) (=== [] Out))
	      ((eq-caro L X) (cdro L Out))
	      (else (fresh (A D Res)
			   (conso A D L)
			   (rembero X D Res)
			   (conso A Res Out)))))

(test-check "4.30"
  (run 1 Out
    (fresh (Y)
	   (rembero peas [a b Y d peas e] Out)))
  [[a b d peas e]])

(test-check "4.31"
  (run* Out
	(fresh (Y Z)
	       (rembero Y [a b Y d Z e] Out)))
  [[b a d (create-var _.0) e]
   [a b d (create-var _.0) e]
   [a b d (create-var _.0) e]
   [a b d (create-var _.0) e]
   [a b (create-var _.0) d e]
   [a b e d (create-var _.0)]
   [a b (create-var _.0) d (create-var _.1) e]])

(test-check "4.49"
  (run* R
    (fresh (Y Z) 
      (rembero Y [Y d Z e] [Y d e])
      (=== [Y Z] R)))
  [[d d]
   [d d]
   [(create-var _.1) (create-var _.1)]
   [e e]])

(test-check "4.57"
  (run 13 W
    (fresh (Y Z Out)
	   (rembero Y [a b Y d Z | W] Out)))
  [(create-var _.0)
   (create-var _.0)
   (create-var _.0)
   (create-var _.0)
   (create-var _.0)
   []
   [(create-var _.0) | (create-var _.1)]
   [(create-var _.0)]
   [(create-var _.0) (create-var _.1) | (create-var _.2)]
   [(create-var _.0) (create-var _.1)]
   [(create-var _.0) (create-var _.1) (create-var _.2) | (create-var _.3)]
   [(create-var _.0) (create-var _.1) (create-var _.2)]
   [(create-var _.0) (create-var _.1) (create-var _.2) (create-var _.3) | (create-var _.4)]])

\* 4.68 *\
(define surpriseo
  { (walkable symbol) --> (query symbol) }
  S -> (rembero S [a b c] [a b c]))

(test-check "4.69"
  (run* R
    (=== d R)
    (surpriseo R))
  [d])

(test-check "4.70"
  (run* R
	(surpriseo R))
  [(create-var _.0)])

(test-check "4.72"
  (run* R
    (=== b R)
    (surpriseo R))
  [b])

\* 5.9 *\
(define appendo
  { (walkable A) --> (walkable A) --> (walkable A) --> (query A) }
  L S Out -> (conde
	      ((nullo L) (=== S Out))
	      (else (fresh (A D Res)
			   (caro L A)
			   (cdro L D)
			   (appendo D S Res)
			   (conso A Res Out)))))

(test-check "5.10"
  (run* X
	(appendo
	 [cake]
	 [tastes yummy]
	 X))
  [[cake tastes yummy]])

(test-check "5.11"
  (run* X
    (fresh (Y)
	   (appendo
	    [cake with ice Y]
	    [tastes yummy]
	    X)))
  [[cake with ice (create-var _.0) tastes yummy]])

(test-check "5.12"
  (run* X
    (fresh (Y)
	   (appendo
	    [cake with ice cream]
	    Y
	    X)))
  [[cake with ice cream | (create-var _.0)]])

(test-check "5.13"
  (run 1 X
    (fresh (Y)
	   (appendo [cake with ice | Y] [d t] X)))
  [[cake with ice d t]])

(test-check "5.14"
  (run 1 Y
    (fresh (X)
	   (appendo [cake with ice | Y] [d t] X)))
  [[]])

\* 5.15 *\ 
(define appendo
  { (walkable A) --> (walkable A) --> (walkable A) --> (query A) }
  L S Out -> (conde
	      ((nullo L) (=== S Out))
	      (else (fresh (A D Res)
			   (conso A D L)
			   (appendo D S Res)
			   (conso A Res Out)))))

(test-check "5.16"
  (run 5 X
    (fresh (Y)
	   (appendo [cake with ice | Y] [d t] X)))
  [[cake with ice d t]
   [cake with ice (create-var _.0) d t]
   [cake with ice (create-var _.0) (create-var _.1) d t]
   [cake with ice (create-var _.0) (create-var _.1) (create-var _.2) d t]
   [cake with ice (create-var _.0) (create-var _.1) (create-var _.2) (create-var _.3) d t]])

(test-check "5.17"
  (run 5 Y
    (fresh (X)
	   (appendo [cake with ice | Y] [d t] X)))
  [[]
   [(create-var _.0)]
   [(create-var _.0) (create-var _.1)]
   [(create-var _.0) (create-var _.1) (create-var _.2)]
   [(create-var _.0) (create-var _.1) (create-var _.2) (create-var _.3)]])

(test-check "5.20"
  (run 5 X
    (fresh (Y)
	   (appendo
	    [cake with ice | Y]
	    [d t | Y]
	    X)))
  [[cake with ice d t]
   [cake with ice (create-var _.1) d t (create-var _.1)]
   [cake with ice (create-var _.2) (create-var _.3) d t (create-var _.2) (create-var _.3)]
   [cake with ice (create-var _.3) (create-var _.4) (create-var _.5) d t (create-var _.3)
	 (create-var _.4) (create-var _.5)]
   [cake with ice (create-var _.4) (create-var _.5) (create-var _.6) (create-var _.7) d t
	 (create-var _.4) (create-var _.5) (create-var _.6) (create-var _.7)]])

\* 5.59 *\ 
(define flatteno
  { (walkable A) --> (walkable A) --> (query A) }
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

(test-check "6.7"
  (run 1 Q
    (alwayso) 
    (=== true Q))
  [true])

(test-check "6.10"
  (run 5 Q
    (alwayso) 
    (=== true Q))
  [true true true true true])

(test-check "6.11"
  (run 5 Q
    (=== true Q) 
    (alwayso))
  [true true true true true])

(define salo
  { (query A) --> (query A) }
  G -> (conde
	(mk-succeed mk-succeed)
	(else G)))

(test-check "6.13"
  (run 1 Q
    (salo (alwayso))
    (=== true Q))
  [true])

(test-check "6.14"
  (run 1 Q
    (salo (nevero))
    (=== true Q))
  [true])

(test-check "6.21"
  (run 5 Q
    (condi                                                                  
      ((=== false Q) (alwayso))                                              
      (else (anyo (=== true Q)))) 
    (=== true Q))
  [true true true true true])

(test-check "6.24"
  (run 5 R
    (condi
      ((teacupo R) mk-succeed)
      ((=== false R) mk-succeed)
      (else mk-fail)))
  [tea false cup])

(test-check "6.25"
  (run 5 Q
    (condi
      ((=== false Q) (alwayso))
      ((=== true Q) (alwayso))
      (else mk-fail))
    (=== true Q))
  [true true true true true])

\* 7.5 *\
(define bit-xoro
  { (walkable number) --> (walkable number) --> (walkable number)
    --> (query number) }
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
   [[1] [1] [0 1]]])

(test-check "7.126"
	    (run* S (fresh (X Y) (addero 0 X Y [1 0 1]) (=== [X Y] S)))
	    [[[1 0 1] []] [[] [1 0 1]] [[1] [0 0 1]] [[0 0 1] [1]]
	     [[1 1] [0 1]] [[0 1] [1 1]]])

(test-check "7.129"
	    (run* S (fresh (X Y) (+o X Y [1 0 1]) (=== [X Y] S)))
	    [[[1 0 1] []] [[] [1 0 1]] [[1] [0 0 1]] [[0 0 1] [1]]
	     [[1 1] [0 1]] [[0 1] [1 1]]])

(test-check "7.131"
	    (run* Q (-o [0 0 0 1] [1 0 1] Q))
	    [[1 1]])

(test-check "7.132"
	    (run* Q (-o [0 1 1] [0 1 1] Q))
	    [[]])

(test-check "8.4"
  (run* P
    (*o [0 1] [0 0 1] P))  
  [[0 0 0 1]])

\* 8.10 *\
(define *o
  { (walkable number) --> (walkable number) --> (walkable number)
    --> (query number) }
  N M P -> (condi
	    ((=== [] N) (=== [] P))
	    ((poso N) (=== [] M) (=== [] P))  
	    ((=== [1] N) (poso M) (=== M P))   
	    ((>lo N) (=== [1] M) (=== N P))
	    ((fresh (X Z)
		    (=== [0 | X] N) (poso X)
		    (=== [0 | Z] P) (poso Z)
		    (>lo M)
		    (*o X M Z)))
	    ((fresh (X Y)
		    (=== [1 | X] N) (poso X)
		    (=== [0 | Y] M) (poso Y)
		    (*o M N P)))
	    ((fresh (X Y)
		    (=== [1 | X] N) (poso X)
		    (=== [1 | Y] M) (poso Y)
		    (odd-*o X N M P)))
	    (else mk-fail)))

(test-check "8.20"
  (run 1 T
    (fresh (N M)
      (*o N M [1])
      (=== [N M] T)))
  [[[1] [1]]])

(test-check "8.23"
  (run 2 T
    (fresh (N M)
      (*o N M [1])
      (=== [N M] T)))
  [[[1] [1]]])

(test-check "8.23"
	    (run 2 T (fresh (N M) (*o N M [1]) (=== [N M] T)))
	    [[[1] [1]]])

(test-check "8.24"
  (run* P (*o [1 1 1] [1 1 1 1 1 1] P))
  [[1 0 0 1 1 1 0 1 1]])

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
