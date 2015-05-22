(datatype option-types
  X : A;
  =====================
  [just X] : (maybe A);

  ____________________
  nothing : (maybe A);)

(datatype protect-type
  __________________________________
  protect : (variable --> variable);)

(datatype variable-type
  N : number;
  =================================================
  (string->symbol (@s "_" "." (str N))) : variable;

  if (mk-variable? V)
  V : symbol;
  ___________________
  V : variable;

  (mk-variable? V) : verified;
  V : symbol;
  ____________________________
  V : variable;)

(synonyms var (variable * number)
	  (substitution A) (var * A))

(datatype walkable-type
  __________________
  [] : (walkable A);

  V : variable;
  T : number;
  =======================
  (@p V T): (walkable A);

  X  : (walkable A);
  Xs : (walkable A);
  ========================
  [X | Xs] : (walkable A);

  __________________________
  X : A >> X : (walkable A);

  ____________________________________________
  X : (variable * number) >> X : (walkable A);

  X : A;
  _________________
  X : (walkable A);)

(datatype datastream
  X : A;
  F : (lazy (datastream A));
  ==========================
  (@p X F) : (datastream A);

  X : A;
  =====================
  [X] : (datastream A);

  ____________________
  [] : (datastream A);)

(synonyms (pairs A) (list (substitution (walkable A)))
	  (query A) ((pairs A) --> (datastream (pairs A))))

(datatype timestamp-instances
  _____________________________
  (value *timestamp*) : number;)
