open import Data.Nat
-- open import Agda.Builtin.Sigma

lemma : {a : ℕ} → a ≤ a
lemma {zero} = z≤n
lemma {suc a} = s≤s lemma

max : ℕ → ℕ → ℕ -- move this elsewhere later...
max zero m = m
max (suc n) zero = suc n
max (suc n) (suc m) = suc (max n m)

data Context : Set  -- A list of types
data _prefix_ : Context → Context → Set
data Type : {n : ℕ} → Context → Set
data InCtx : {n : ℕ} → (Γ : Context) → {Γ' : Context} → Type {n} Γ' → Set
data Value : {n : ℕ} → (Γ : Context) → (t : Type {n} Γ) → Set
data UnApp : {n : ℕ} → (Γ : Context) → (t : Type {n} Γ) → Set

data Context where -- A list of types
  ∅ : Context
  ConsCtx : ∀ {n Γ Γ'} → Γ' prefix Γ → Type {n} Γ' → Context

data _prefix_ where
  same : {Γ : Context} → Γ prefix Γ
  step : {n : ℕ} → ∀{Γ' Γ T} → (p : Γ' prefix Γ) →  Γ' prefix (ConsCtx {n} p T)

data Type where
  U : {n : ℕ} → {Γ : Context} → Type {suc n} Γ
  Pi : ∀ {i j k Γ} → (i ≤ k) → (i ≤ k) → (A : Type {i} Γ) → (B : Type {j} (ConsCtx {i} {Γ} {Γ} same A)) → Type {k} Γ
  fromValue : ∀ {n Γ} → Value {suc n} Γ (U {n}) → Type {n} Γ


data InCtx where
  End : ∀ {Γ n} → {T : Type {n} Γ} → InCtx {n} (ConsCtx same T) {Γ} T
  Before : ∀ {Γ'A Γ'T Γ n} → {A : Type {n} Γ'A} → {T : Type {n} Γ'T} → {p : Γ'T prefix Γ} → InCtx Γ A
    → InCtx {n} (ConsCtx {n} (step {n} {Γ'T} {Γ} {T} p) T) {Γ'A} A
    -- A is the thing thats in the context. T is on end.

-- redundancy in InCtx and prefix, leads to some annoyance later.
-- idea:
data InCtx2 : {n : ℕ} → (Γ : Context) → {Γ' : Context} → Type {n} Γ' → Set where
  inctx2 : ∀{n Γ' Γ T} → (p : Γ' prefix Γ) → (ConsCtx {n} p T) prefix Γ → InCtx2 Γ T


-- inCtxToPrefix : ∀ {n Γ' Γ T} → InCtx {n} Γ {Γ'} T → Γ' prefix Γ
-- inCtxToPrefix End = (step same)
-- inCtxToPrefix (Before {Γ'} {Γ} {n} {T} {p} i) = {!   !}


data Value where
  Lambda : ∀ {n Γ A B} → Value {n} (ConsCtx {n} same A) B → Value Γ (Pi {n} {n} {n} lemma lemma A B)
  fromU : ∀ {n Γ T} → UnApp {n} Γ T → Value {n} Γ T
  fromType : ∀ {n Γ} → Type {n} Γ → Value {suc n} Γ (U {n})

subCtx : ∀ {n Γ' T} → (Γ : Context) → (i : InCtx {n} Γ {Γ'} T) → (v : Value {n} Γ' T)
  → Context

subType : ∀{n m Γ' T} → (Γ : Context) → (i : InCtx {n} Γ {Γ'} T)
  → (A : Type {m} Γ) → (v : Value {n} Γ' T) → Type {m} (subCtx Γ i v)
sub : ∀{n m Γ' T} → (Γ : Context) → (i : InCtx {n} Γ {Γ'} T)
  → {A : Type {m} Γ} → (e : Value Γ A) → (v : Value {n} Γ' T)
    → Value (subCtx Γ i v) (subType Γ i A v)
-- sub : ∀{n m Γ} → {A : Type {n} Γ} → {B : Type {m} (ConsCtx same A)}
  -- (v : Value (ConsCtx {n} same A) B) → (v₀ : Value Γ A) → Value Γ (subType B v₀)

-- T is on end of context Γ, A is being substituted for.
-- (Γ'sub : Context, psub : Γ'sub prefix (subType Γ i T v), Tsub : Type Γ'sub)
data 3Tuple : ∀ {nA nT Γ'T Γ'A A} → (Γ : Context) → (T : Type {nT} Γ'T)
  → (v : Value {nA} Γ'A A) → (i : InCtx {nA} Γ {Γ'A} A) → Set where
  _,_,_ : ∀ {nA nT Γ Γ'T Γ'A} → {T : Type {nT} Γ'T} → {A : Type {nA} Γ'A}
    → {i : InCtx {nA} Γ {Γ'A} A} → ∀ {v} → (Γ'sub : Context)
    → (psub : Γ'sub prefix (subCtx {nA} Γ i v)) → (Tsub : Type {nT} Γ'sub) → 3Tuple Γ T v i
-- should call Γ'sub instead Γ'Tsub

-- subPrefix takes a Γ' prefix Γ and a type T in context Γ' and a substitution of Γ
-- It returns a modified Γ'sub which is a prefix of Γ after the substitution. this
-- may be equal to Γ' or a substitution of it depending on where the substitution is.
-- It also returns Tsub and psub, which are versions of T and the prefix that work after
-- the substitution.

subPrefix : ∀ {nA nT Γ'T Γ'A Γ A} → (p : Γ'T prefix Γ) → (i : InCtx {nA} Γ {Γ'A} A)
  → (T : Type {nT} Γ'T) → (v : Value {nA} Γ'A A) → 3Tuple {nA} {nT} Γ T v i
-- In this case, A is on end of context, so A = T i guess?
subPrefix {nA} {nT} {Γ'T} {Γ'A} {Γ} {A} same i T v = (subCtx Γ'T i v) , same , (subType Γ i T v)
subPrefix {nA} {nT} {Γ'T} {Γ'A} {ConsCtx same A} {A} (step same) End T v
  = (Γ'A , {!   !} , T)
subPrefix {nA} {nT} {Γ'T} {Γ'A} {Γ} {A} (step p) (Before i) T v
  = ( {!   !} , {!   !} , {!   !} )
  -- = {!   !} -- ({!   !} ,  {!   !} , ?) -- recursion with subPrefix

subCtx (ConsCtx {n} {Γ} {Γ'} same _) End v = Γ
subCtx (ConsCtx (step pT) T) (Before {Γ'A} {Γ'T} {Γ} {n} {A} i) v with (subPrefix pT i T v)
...                                                                  | (Γ'Tsub , psub , Tsub)
  = Γ
  -- = ConsCtx {?} {subCtx Γ i {!   !}} {Γ'Tsub} psub Tsub
-- Will need a subvalue for subbing v in prefix of context

-- subType Γ i U v = U
-- subType {n} {m} {Γ'} {T} Γ inctx (Pi {i} {j} {m} {Γ₁} x p A B) v =
  -- Pi x p (subType Γ inctx A v) (subType (ConsCtx same (subType Γ inctx A v)) (Before inctx) {!   !} ?) -- (subType {n} {j} {Γ'} {T} ? ? ? ?)
-- subType Γ i (fromValue x) v = {!   !}
subType = {!   !}
sub = {!   !}


-- it should be that Γ₁ = Γ, but instead Γ'' = Γ'


-- PROBLEM: the fact it doens't know that Γ₁ = Γ is because there is redudant
-- informaiton in ConsCtx/prfix/InCtx


data UnApp where
  Var : ∀ {n Γ T} → InCtx {n} Γ T → UnApp Γ T
  -- TODO: replace m in A with n
  -- TODO: also, should all three of those really be m?
  App : ∀ {m Γ} → {A : Type {m} Γ} → {B : Type {m} (ConsCtx same A)} → UnApp Γ (Pi {m} {m} {m} lemma lemma A B) →
    (x : Value Γ A) → UnApp Γ {!   !} --(subType (ConsCtx same A) End B x)


-- subType {n} {m} {Γ} {A} U v₀ = U
-- subType {n} {m} {Γ} {A} (Pi {i j k} A B) v₀ = ?
-- subType {n} {m} {Γ} {A} (fromValue x) v₀ = {!   !}
-- subType {n} {m} {Γ} {A} U v₀ =  U
-- subType {n} {m} {Γ} {A} (Pi {i} {j} p1 p2 X Y) v₀
  -- = Pi p1 p2 (subType X v₀) {!   !}
-- subType {n} {m} {Γ} {A} (fromValue v) v₀ = {!   !}
-- sub v v₀ = {! v  !}

-- TODO: dont require m to be same for A and v

-- TODO: reffering to my latex writup, make the whole language in Agda!!!!!!!
