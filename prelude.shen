(define caro
  { (walkable A) --> (walkable A) --> (query A) } 
  P H -> (fresh (T) (=== [H | T] P)))

(define cdro
  { (walkable A) --> (walkable A) --> (query A) } 
  P T -> (fresh (H) (=== [H | T] P)))

(define conso
  { (walkable A) --> (walkable A) --> (walkable A) --> (query A) } 
  H T P -> (=== [H | T] P))

(define nullo
  { (walkable A) --> (query A) }
  X -> (=== [] X))

(define eqo
  { (walkable A) --> (walkable A) --> (query A) }
  X Y -> (=== X Y))

(define eq-caro
  { (walkable A) --> (walkable A) --> (query A) }
  L X -> (caro L X))

(define pairo
  { (walkable A) --> (query A) }
  P -> (fresh (A D) (conso A D P)))

(define listo
  { (walkable A) --> (query A) }
  L -> (conde
	((nullo L) mk-succeed)
	((pairo L) (fresh (D)
			  (cdro L D)
			  (listo D)))
	(else mk-fail)))

(define membero
  { (walkable A) --> (walkable A) --> (query A) }
  X L -> (conde ((nullo L) mk-fail)
		((eq-caro L X) mk-succeed)
		(else (fresh (D)
			     (cdro L D)
			     (membero X D)))))

(define rembero
  { (walkable A) --> (walkable A) --> (walkable A) --> (pairs A)
                 --> (datastream (pairs A)) }
  X L Out -> (conde ((nullo L) (=== [] Out))
		    ((eq-caro L X) (cdro L Out))
		    (else (fresh (A D Res)
				 (conso A D L)
				 (rembero X D Res)
				 (conso A Res Out)))))

(define appendo
  { (walkable A) --> (walkable A) --> (walkable A) --> (pairs A)
    --> (datastream (pairs A)) }
  L S Out -> (conde ((nullo L) (=== S Out))
		    (else (fresh (A D Res)
				 (conso A D L)
				 (conso A Res Out)
				 (appendo D S Res)))))

(define anyo
  { (query A) --> (query A) }
  G -> (conde (G mk-succeed)
	      (else (anyo G))))

(define nevero
  { --> (query A) }
  -> (anyo mk-fail))

(define alwayso
  { --> (query A) }
  -> (anyo mk-succeed))

(define full-addero
  { (walkable number) --> (walkable number) --> (walkable number)
    --> (walkable number) --> (walkable number)
    --> (query number) }
  B X Y R C -> (conde
		((=== 0 B) (=== 0 X) (=== 0 Y) (=== 0 R) (=== 0 C))
		((=== 1 B) (=== 0 X) (=== 0 Y) (=== 1 R) (=== 0 C))
		((=== 0 B) (=== 1 X) (=== 0 Y) (=== 1 R) (=== 0 C))
		((=== 1 B) (=== 1 X) (=== 0 Y) (=== 0 R) (=== 1 C))
		((=== 0 B) (=== 0 X) (=== 1 Y) (=== 1 R) (=== 0 C))
		((=== 1 B) (=== 0 X) (=== 1 Y) (=== 0 R) (=== 1 C))
		((=== 0 B) (=== 1 X) (=== 1 Y) (=== 0 R) (=== 1 C))
		((=== 1 B) (=== 1 X) (=== 1 Y) (=== 1 R) (=== 1 C))
		(else mk-fail)))

(define poso
  { (walkable A) --> (query A) }
  N -> (fresh (A D) (=== [A | D] N)))

(define >lo
  { (walkable A) --> (query A) }
  N -> (fresh (A AD DD) (=== [A AD | DD] N)))

(define gen-addero
  { (walkable number) --> (walkable number) --> (walkable number)
    --> (walkable number) --> (query number)}
  D N M R -> (fresh (A B C E X Y Z)
		    (=== [A | X] N)
		    (=== [B | Y] M) (poso Y)
		    (=== [C | Z] R) (poso Z)
		    (alli
		     (full-addero D A B C E)
		     (addero E X Y Z))))

(define addero
  { (walkable number) --> (walkable number) --> (walkable number)
    --> (walkable number) --> (query number)}
  D N M R -> (condi
	      ((=== 0 D) (=== [] M) (=== N R))
	      ((=== 0 D) (=== [] N) (=== M R)
	       (poso M))
	      ((=== 1 D) (=== [] M)
	       (addero 0 N [1] R))
	      ((=== [1] N) (=== [1] M)
	       (fresh (A C)
		      (=== [A | C]  R)
		      (full-addero D 1 1 A C)))
	      ((=== [1] N) (gen-addero D N M R))
	      ((=== [1] M) (>lo N) (>lo R)
	       (addero D [1] N R))
	      ((>lo N) (gen-addero D N M R))
	      (else mk-fail)))

(define +o
  { (walkable number) --> (walkable number) --> (walkable number)
    --> (query number) }
  N M K -> (addero (wval 0) N M K))

(define -o
  { (walkable number) --> (walkable number) --> (walkable number)
    --> (query number) }
  N M K -> (+o M K N))

(define *o
  { (walkable number) --> (walkable number) --> (walkable number)
    --> (query number) }
  N M P -> (condi ((=== [] N) (=== [] P))
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

(define odd-*o
  { (walkable number) --> (walkable number) --> (walkable number)
    --> (walkable number) --> (query number) }
  X N M P -> (fresh (Q)
		    (bound-*o Q P N M)
		    (*o X M Q)
		    (+o [0 | Q] M P)))
(define bound-*o
  { (walkable number) --> (walkable number) --> (walkable number)
    --> (walkable number) --> (query number) }
  Q P N M -> (conde ((nullo Q) (pairo P))
		    (else (fresh (X Y Z)
				 (cdro Q X)
				 (cdro P Y)
				 (condi
				  ((nullo N)
				   (cdro M Z)
				   (bound-*o X Y Z []))
				  (else
				   (cdro N Z)
				   (bound-*o X Y Z M)))))))

(define =lo
  { (walkable number) --> (walkable number)
    --> (query number) }
  N M -> (conde
	  ((=== [] N) (=== [] M))
	  ((=== [1] N) (=== [1] M))
	  (else (fresh (A X B Y)
		       (=== [A | X] N) (poso X)
		       (=== [B | Y] M) (poso Y)
		       (=lo X Y)))))

(define <lo
  { (walkable number) --> (walkable number)
    --> (query number) }
  N M -> (conde
	  ((=== [] N) (poso M))
	  ((=== [1] N) (>lo M))
	  (else (fresh (A X B Y)
		       (=== [A | X] N) (poso X)
		       (=== [B | Y] M) (poso Y)
		       (<lo X Y)))))

(define <=lo
  { (walkable number) --> (walkable number)
    --> (query number) }
  N M -> (condi ((=lo N M) mk-succeed)
		((<lo N M) mk-succeed)
		(else mk-fail)))

(define <o
  { (walkable number) --> (walkable number)
    --> (query number) }
  N M -> (condi ((<lo N M) mk-succeed)
		((=lo N M) (fresh (X)
				  (poso X)
				  (+o N X M)))
		(else mk-fail)))

(define <=o
  { (walkable number) --> (walkable number)
    --> (query number) }
  N M -> (condi ((=== N M) mk-succeed)
		((<o N M)  mk-succeed)
		(else mk-fail)))

(define splito
  { (walkable number) --> (walkable number) --> (walkable number)
    --> (walkable number) --> (query number) }
  N R L H -> (condi
	      ((=== [] N) (=== [] H) (=== [] L))
	      ((fresh (B NH)
		      (=== [0 B | NH] N)
		      (=== [] R)
		      (=== [0 B | NH] H)
		      (=== [] L)))
	      ((fresh (NH)
		      (=== [1 | NH] N)
		      (=== [] R)
		      (=== NH H)
		      (=== [1] L)))
	      ((fresh (B NH A RH)
		      (=== [0 B | NH] N)
		      (=== [A | RH] R)
		      (=== [] L)
		      (splito [B | NH] RH [] H)))
	      ((fresh (NH A RH)
		      (=== [1 | NH] N)
		      (=== [A | RH] R)
		      (=== [1] L)
		      (splito NH RH [] H)))
	      ((fresh (B NH A RH LH)
		      (=== [B | NH] N)
		      (=== [A | RH] R)
		      (=== [B | LH] L)
		      (poso LH)
		      (splito NH RH LH H)))
	      (else mk-fail)))

(define /o
  { (walkable number) --> (walkable number) --> (walkable number)
    --> (walkable number) --> (query number) }
  N M Q R -> (condi
	      ((=== R N) (=== [] Q) (<o N M))
	      ((=== [1] Q) (=lo N M) (+o R M N)
	       (<o R M))
	      (else
	       (alli
		(<lo M N)
		(<o R M)
		(poso Q)
		(fresh (NH NL QH QL QLM QLMR RR RH)
		       (alli
			(splito N R NL NH)
			(splito Q R QL QH)
			(conde
			 ((=== [] NH)
			  (=== [] QH)
			  (-o NL R QLM)
			  (*o QL M QLM))
			 (else
			  (alli
			   (poso NH)
			   (*o QL M QLM)
			   (+o QLM R QLMR)
			   (-o QLMR NL RR)
			   (splito RR R [] RH)
			   (/o NH M QH RH))))))))))

(define repeated-mul
  { (walkable number) --> (walkable number) --> (walkable number)
    --> (query number) }
  N Q NQ -> (conde
	     ((poso N) (=== [] Q) (=== [1] NQ))
	     ((=== [1] Q) (=== N NQ))
	     ((>lo Q)
	      (fresh (Q1 NQ1)
		     (+o Q1 [1] Q)
		     (repeated-mul N Q1 NQ1)
		     (*o NQ1 N NQ)))
	     (else mk-fail)))

(define exp2
  { (walkable number) --> (walkable number) --> (walkable number)
    --> (query number) }
  N B Q -> (condi
	    ((=== [1] N) (=== [] Q))
	    ((>lo N) (=== [1] Q)
	     (fresh (S)
		    (splito N B S [1])))
	    ((fresh (Q1 B2)
		    (alli
		     (=== [0 | Q1] Q)
		     (poso Q)
		     (<lo B N)
		     (appendo B [1 | B] B2)
		     (exp2 N B2 Q1))))
	    ((fresh (Q1 NH B2 S)
		    (alli
		     (=== [1 | Q1] Q)
		     (poso Q1)
		     (poso NH)
		     (splito N B S NH)
		     (appendo B [1 | B] B2)
		     (exp2 NH B2 Q1))))
	    (else mk-fail)))
