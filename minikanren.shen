(set *timestamp* 0)

(define assq
  { A --> (list (A * B)) --> (maybe B) }
  X [(@p X Y) | _] -> [just Y]
  X [_ | Ps]       -> (assq X Ps)
  _ []             -> nothing)

(define maybe
  { B --> (A --> B) --> (maybe A) --> B }
  D F nothing  -> D
  _ F [just X] -> (F X))

(define reified-name?
  { string --> boolean }
  (@s "_" "." _) -> true
  _ -> false)

(define mk-variable?
  { symbol --> boolean }
  V -> true where (or (variable? V) (reified-name? (str V)))
  _ -> false)

(define var
  { variable --> var }
  V -> (let T (value *timestamp*)
	 (do (set *timestamp* (+ T 1))
	     (@p V T))))

(define empty-s
  { --> (list (substitution A)) }
  -> [])

(define ext-s
  { var --> A --> (list (substitution A)) --> (list (substitution A))}
  X V S -> [(@p X V) | S])

(define wvar
  { var --> (walkable A) }
  V -> V)

(define create-var
  { variable --> (walkable A) }
  V -> (wvar (var V)))

(define walk
  { (walkable A) --> (pairs A) --> (walkable A) }
  (@p V T) S -> (maybe (@p V T) (/. W (walk W S)) (assq (@p V T) S))
  W _        -> W)

(define mk-=
  { (walkable A) --> (walkable A) --> boolean }
  (@p V _) (@p V _) -> true
  V W -> (= V W))

(define mk-unify-
  { (walkable A) --> (walkable A) --> (pairs A) --> (maybe (pairs A)) }
  V V S        -> [just S]
  (@p V T) W S -> [just (ext-s (@p V T) W S)]
  V (@p W T) S -> [just (ext-s (@p W T) V S)]
  [V | Vs] [W | Ws] S -> (maybe nothing
				(mk-unify Vs Ws)
				(mk-unify V W S))
  V W S -> [just S] where (mk-= V W)
  _ _ _ -> nothing)

(define mk-unify
  { (walkable A) --> (walkable A) --> (pairs A) --> (maybe (pairs A)) }
  V W S -> (mk-unify- (walk V S) (walk W S) S))

(define mk-occurs-check
  { (walkable A) --> (walkable A) --> (pairs A) --> boolean }
  X V S -> (mk-occurs-check- X (walk V S) S))

(define mk-occurs-check-
  { (walkable A) --> (walkable A) --> (pairs A) --> boolean }
  (@p V T) (@p V T) S -> true
  V [W | Ws] S        -> (or (mk-occurs-check V W S)
			     (mk-occurs-check V Ws S))
  _ _ _ -> false)

(define ext-s-check
  { var --> (walkable A) --> (pairs A) --> (maybe (pairs A)) }
  (@p V T) W S -> nothing where (mk-occurs-check (@p V T) W S)
  (@p V T) W S -> [just (ext-s (@p V T) W S)])

(define mk-unify-check-
  { (walkable A) --> (walkable A) --> (pairs A) --> (maybe (pairs A)) }
  V V S -> [just S]
  (@p V T) W S -> (ext-s-check (@p V T) W S)
  V (@p W T) S -> (ext-s-check (@p W T) V S)
  [V | Vs] [W | Ws] S -> (maybe nothing
				(mk-unify-check Vs Ws)
				(mk-unify-check V W S))
  V W S -> [just S] where (mk-= V W)
  _ _ _ -> nothing)

(define mk-unify-check
  { (walkable A) --> (walkable A) --> (pairs A) --> (maybe (pairs A)) }
  V W S -> (mk-unify-check- (walk V S) (walk W S) S))

(define walk*-
  { (walkable A) --> (pairs A) --> (walkable A) }
  (@p V T) S -> (@p V T)
  [V | Vs] S -> [(walk* V S) | (walk* Vs S)]
  V _ -> V)

(define walk*
  { (walkable A) --> (pairs A) --> (walkable A) }
  V S -> (walk*- (walk V S) S))

(define reify-name
  { number --> var }
  N -> (var (string->symbol (@s "_" "." (str N)))))

(define reify-s-
  { (walkable A) --> (pairs A) --> (pairs A) }
  (@p V T) S -> (let W (reify-name (size-s S))
		  (ext-s (@p V T) W S))
  [V | Vs] S -> (reify-s Vs (reify-s V S))
  _ S -> S)

(define reify-s
  { (walkable A) --> (pairs A) --> (pairs A) }
  V S -> (reify-s- (walk V S) S))

(define reify
  { (walkable A) --> (walkable A) }
  W -> (walk* W (reify-s W (empty-s))))

(define mk-fail
  { A --> (datastream A) }
  _ -> [])

(define mk-succeed
  { A --> (datastream A) }
  S -> [S])

(define ===
  { (walkable A) --> (walkable A) --> (query A) }
  V W S -> (maybe [] mk-succeed (mk-unify V W S)))

(define ===-check
  { (walkable A) --> (walkable A) --> (query A) }
  V W S -> (maybe [] mk-succeed (mk-unify-check V W S)))

(define map-inf
  { (maybe number)
    --> ((pairs A) --> (walkable A))
    --> (datastream (pairs A))
    --> (list (walkable A)) }
  _ _ []  -> []
  _ P [X] -> [(P X)]
  nothing  P (@p X F) -> [(P X) | (map-inf nothing P (thaw F))]
  [just N] P (@p X F) -> [(P X) | (map-inf [just (- N 1)] P (thaw F))]
                         where (> N 1)
  _ P (@p X F) -> [(P X)])

(define mk-bind
  { (datastream A) --> (A --> (datastream B)) --> (datastream B) }
  [] G  -> []
  [X] G -> (G X)
  (@p X F) G -> (mplus (G X) (freeze (mk-bind (thaw F) G))))

(define mplus
  { (datastream A) --> (lazy (datastream A)) --> (datastream A) }
  [] G  -> (thaw G)
  [X] G -> (@p X G)
  (@p X F) G -> (@p X (freeze (mplus (thaw F) G))))

(define mplusi
  { (datastream A) --> (lazy (datastream A)) --> (datastream A) }
  [] F  -> (thaw F)
  [X] F -> (@p X F)
  (@p X F) G -> (@p X (freeze (mplusi (thaw G) F))))

(define mk-bindi
  { (datastream A) --> (A --> (datastream B)) --> (datastream B) }
  [] G  -> []
  [X] G -> (G X)
  (@p X F) G -> (mplusi (G X) (freeze (mk-bindi (thaw F) G))))

(defmacro conde-macro
  [conde] -> [mk-fail]
  [conde [else G | Gs]]   -> [all G | Gs]
  [conde [G | Gs] | Cs] -> [anye [all G | Gs] [conde | Cs]])

(defmacro anye-macro
  [anye G1 G2] -> (let S (gensym (protect S))
		    [lambdag@ S [mplus [G1 S] [lambdaf@ [G2 S]]]]))

(defmacro alli-macro
  [alli] -> [mk-succeed]
  [alli G] -> (let S (gensym (protect S))
		[lambdag@ S [G S]])
  [alli G1 | Gs] -> (let S (gensym (protect S))
		      [lambdag@ S [mk-bindi [G1 S] [alli | Gs]]]))

(defmacro anyi-macro
  [anyi G1 G2] -> (let S (gensym (protect S))
		    [lambdag@ S [mplusi [G1 S] [lambdaf@ [G2 S]]]]))

(defmacro condi-macro
  [condi] -> [mk-fail]
  [condi [else G | Gs]] -> [all G | Gs]
  [condi [G | Gs] | Cs] -> [anyi [all G | Gs] [condi | Cs]])

(define ifa-impl-
  { (datastream (pairs A)) --> (query A) --> (query A) --> (query A) }
  [] G1 G2 S      -> (G2 S)
  [S] G1 _ _      -> (G1 S)
  (@p S F) G1 _ _ -> (mk-bind (@p S F) G1))

(define ifa-impl
  { (query A) --> (query A) --> (query A) --> (query A) }
  G0 G1 G2 S -> (ifa-impl- (G0 S) G1 G2 S))

(defmacro ifa-macro
  [ifa G0 G1 G2] -> [ifa-impl G0 G1 G2])

(defmacro conda-macro
  [conda] -> [mk-fail]
  [conda [else G | Gs]] -> [all G | Gs]
  [conda [G0 G | Gs] C | Cs] -> [ifa G0 [all G | Gs] [conda C | Cs]])

(define ifu-impl-
  { (datastream (pairs A)) --> (query A) --> (query A) --> (query A) }
  [] G1 G2 S      -> (G2 S)
  [S] G1 G2 _     -> (G1 S)
  (@p S F) G1 _ _ -> (G1 S))

(define ifu-impl
  { (query A) --> (query A) --> (query A) --> (query A) }
  G0 G1 G2 S -> (ifu-impl- (G0 S) G1 G2 S))

(defmacro ifu-macro
  [ifu G0 G1 G2] -> [ifu-impl G0 G1 G2])

(defmacro condu-macro
  [condu] -> [mk-fail]
  [condu [else G | Gs]] -> [all G | Gs]
  [condu [G0 G| Gs] C | Cs] -> [ifu G0 [all G | Gs] [condu C | Cs]])
