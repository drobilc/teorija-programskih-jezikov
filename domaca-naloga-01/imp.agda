module imp where


-- Logične vrednosti

data Bool : Set where
    true : Bool
    false : Bool

if_then_else_ : {A : Set} → Bool → A → A → A
if true then x else y = x
if false then x else y = y


-- Naravna števila

data Nat : Set where
    zero : Nat
    suc : Nat → Nat 

-- Namesto suc (suc zero) lahko napišemo kar 2
{-# BUILTIN NATURAL Nat #-}

plus : Nat → Nat → Nat
plus zero n = n
plus (suc m) n = suc (plus m n)

mul : Nat → Nat → Nat
mul m zero = zero
mul m (suc n) = plus m (mul m n)

pow : Nat → Nat → Nat
pow m zero = suc zero
pow m (suc n) = mul m (pow m n)

eq : Nat → Nat → Bool
eq zero zero = true
eq (suc n) zero = false
eq zero (suc n) = false
eq (suc m) (suc n) = eq m n

le : Nat → Nat → Bool
le zero zero = false
le (suc x) zero = false
le zero (suc y) = true
le (suc x) (suc y) = le x y

ge : Nat → Nat → Bool
ge zero zero = false
ge (suc x) zero = true
ge zero (suc y) = false
ge (suc x) (suc y) = ge x y

-- Seznami

data List : Set → Set where
    [] : {A : Set} → List A
    _::_ : {A : Set} → A → List A → List A

_++_ : {A : Set} → List A → List A → List A
[] ++ snd = snd
(x :: fst) ++ snd = x :: (fst ++ snd)

-- Končne množice

data Fin : Nat → Set where
    zero : {n : Nat} → Fin (suc n)
    suc : {n : Nat} → Fin n → Fin (suc n)

infixl 25 _/_

_/_ : (m n : Nat) → Fin (suc (plus m n))
zero / n = zero
suc m / n = suc (m / n)


-- Vektorji

data Vec : Set → Nat → Set where
    [] : {A : Set} → Vec A zero
    _::_ : {A : Set} {n : Nat} → A → Vec A n → Vec A (suc n)

_[_] : {A : Set} {n : Nat} → Vec A n → Fin n → A
[] [ () ]
(x :: v) [ zero ] = x
(x :: v) [ suc ind ] = v [ ind ]

_[_]←_ : {A : Set} {n : Nat} → Vec A n → Fin n → A → Vec A n
_[_]←_ [] ()
_[_]←_ (x :: xs) zero v = v :: xs
_[_]←_ (x :: xs) (suc i) v = x :: (xs [ i ]← v)


-- Sintaksa jezika

infixr 3 _；_ 
infix 4 _:=_
infix 5 IF_THEN_ELSE_END
infix 6 WHILE_DO_DONE
infix 6 SKIP
infix 6 PRINT_

infixl 8 _OR_
infixl 9 _AND_

infix 10 _≡_
infix 10 _>_
infix 10 _<_

infixl 11 _+_
infixl 12 _*_
infixr 13 _**_

infix 14 !_
infix 15 `_

-- Artimetične in logične izraze ter ukaze parametriziramo z naravnim številom `n`,
-- ki pove, da izraz uporablja spremenljivke indeksirane med `0` in `n - 1`.

data Exp (n : Nat) : Set where
    `_ : Nat → Exp n
    !_ : Fin n → Exp n -- Spremenljivke nazivamo z naravnimi števili manjšimi od `n`
    _+_ : Exp n → Exp n → Exp n
    _*_ : Exp n → Exp n → Exp n
    _**_ : Exp n → Exp n → Exp n

data BExp (n : Nat) : Set where
    _≡_ : Exp n → Exp n → BExp n
    _<_ : Exp n → Exp n → BExp n
    _>_ : Exp n → Exp n → BExp n
    NOT_ : BExp n → BExp n
    _AND_ : BExp n → BExp n → BExp n
    _OR_ : BExp n → BExp n → BExp n

data Cmd : (n : Nat) → Set where
    IF_THEN_ELSE_END : {n : Nat} → BExp n → Cmd n → Cmd n → Cmd n
    WHILE_DO_DONE : {n : Nat} → BExp n → Cmd n → Cmd n
    FOR_:=_TO_DO_DONE : {n : Nat} → (Fin n) → Exp n → Exp n → Cmd n → Cmd n
    _；_ : {n : Nat} → Cmd n → Cmd n → Cmd n
    _:=_ : {n : Nat} → (Fin n) → Exp n → Cmd n
    SKIP : {n : Nat} → Cmd n
    PRINT_ : { n : Nat } → Exp n → Cmd n

-- Primer aritmetičnega izraza, ki sešteje vrednosti spremenljivk na mestu 1 in 0 v stanju s tremi spremenljivkami. 
primer : Exp 3
primer = ! 1 / 1 + ! 0 / 2 -- Da lahko uporabimo vrednost na mestu 0 in 1 v izrazu velikosti do 3.

-- Program, ki sešteje prvih n naravnih števil
-- vsota : Nat → Cmd 3
-- vsota n = 
--     0 / 2 := ` n ； -- Indeksiramo prvo spremenljivo, in tip vseh možnih spremenljivk povečamo za 2, saj bomo v celotnem programo potrebovali tri spremenljivke
--     1 / 1 := ` 0 ；
--     2 / 0 :=  ! (0 / 2) ；
--     WHILE ! (1 / 1) < ! (0 / 2) DO
--         2 / 0 := ! 2 / 0 + ! 1 / 1 ；
--         1 / 1 := ! 1 / 1 + ` 1
--     DONE

-- Program, ki sešteje prvih n naravnih števil s pomočjo for zanke
vsota : Nat → Cmd 3
vsota n = 
    0 / 2 := ` n ； -- Indeksiramo prvo spremenljivo, in tip vseh možnih spremenljivk povečamo za 2, saj bomo v celotnem programo potrebovali tri spremenljivke
    1 / 1 := ` 0 ；
    2 / 0 := ` 0 ；
    FOR ( (1 / 1) ) := ` 1 TO ! (0 / 2) DO
        2 / 0 := ! 2 / 0 + ! 1 / 1 ；
        1 / 1 := ! 1 / 1 + ` 1 ； PRINT (! (2 / 0))
    DONE

-- Stanje

State : Nat → Set
State n = Vec Nat n

-- Result : Nat → Set
-- Result n = State n

-- Če želite, lahko za nadgradnjo rezultatov uporabite spodnje tipe

record Pair (A B : Set) : Set where
    constructor _,_
    field
        fst : A
        snd : B

-- Result : Nat → Set
-- Result n = Pair (State n) (List Nat)

data Maybe (A : Set) : Set where
    nothing : Maybe A
    just : A → Maybe A

Result : Nat → Set
Result n = Pair (Maybe (State n)) (List Nat)

evalExp : {n : Nat} → State n → Exp n → Nat
evalExp st (` x) = x
evalExp st (! i) = st [ i ]
evalExp st (exp₁ + exp₂) = plus (evalExp st exp₁) (evalExp st exp₂)
evalExp st (exp₁ * exp₂) = mul (evalExp st exp₁) (evalExp st exp₂)
evalExp st (exp₁ ** exp₂) = pow (evalExp st exp₁) (evalExp st exp₂)

evalBExp : {n : Nat} → State n → BExp n → Bool
evalBExp st (exp₁ ≡ exp₂) = eq (evalExp st exp₁) (evalExp st exp₂)
evalBExp st (exp₁ < exp₂) = le (evalExp st exp₁) (evalExp st exp₂)
evalBExp st (exp₁ > exp₂) = ge (evalExp st exp₁) (evalExp st exp₂)
evalBExp st (NOT bExp) = if (evalBExp st bExp) then false else true
evalBExp st (exp₁ AND exp₂) = if (evalBExp st exp₁) then (evalBExp st exp₂) else false
evalBExp st (exp₁ OR exp₂) = if (evalBExp st exp₁) then true else (evalBExp st exp₂)

evalStmt : {n : Nat} → Nat → Maybe (State n) → Cmd n → Result n

evalStmt _ nothing _ = nothing , []

evalStmt n (just st) IF bexp THEN cmd₁ ELSE cmd₂ END =
    if (evalBExp st bexp)
    then (evalStmt n (just st) cmd₁)
    else (evalStmt n (just st) cmd₂)

evalStmt (suc n) (just st) WHILE bexp DO cmd DONE =
    if evalBExp st bexp
    then (
        let (state , print) = (evalStmt n (just st) cmd) in -- Izvedemo eno iteracijo telesa zanke
        let (stateAfter , printAfter) = (evalStmt n state (WHILE bexp DO cmd DONE)) in 
        (stateAfter , (print ++ printAfter))
    )
    else ((just st) , []) -- Prisli smo do zadnje iteracije

evalStmt (suc n) (just st) (FOR ℓ := start TO end DO cmd DONE) =
    evalStmt n (just st) (ℓ := start ； WHILE ! ℓ < end DO cmd DONE)

evalStmt n (just st) (cmd₁ ； cmd₂) =
    let (state₁ , print₁) = (evalStmt n (just st) cmd₁) in
    let (state₂ , print₂) = (evalStmt n state₁ cmd₂) in
    state₂ , (print₁ ++ print₂)

evalStmt _ (just st) (ℓ := exp) = just ( st [ ℓ ]← (evalExp st exp) ) , []
evalStmt _ (just st) SKIP = just st , []
evalStmt _ (just st) (PRINT exp) = just st , ((evalExp st exp) :: [])

evalStmt zero (just st) (FOR ℓ := start TO end DO cmd DONE) = nothing , [] -- For zanki je zmanjkalo goriva
evalStmt zero (just st) (WHILE bexp DO cmd DONE) = nothing , [] -- While zanki je zmanjkalo goriva

evalCmd : {n : Nat} → Nat → State n → Cmd n → Result n
evalCmd n st cmd = evalStmt n (just st) cmd