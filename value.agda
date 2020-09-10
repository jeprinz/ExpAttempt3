open import Data.Nat

lemma : {a : ℕ} → a ≤ a
lemma = {!   !}

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

-- T is type in context that is being substituted
-- A is on end of context, so A ≠ T.
-- However, agda thinks that A = T. Why?
-- Γ' is context of T
-- Γ1 is context to the left of A
-- Γ2 is context of A

--It should be the case that Γ = Γ1, and Γ' ≠ Γ2
-- also, pT ≠ pA

-- subCtx (ConsCtx {n} {Γ} {Γ'} same _) End v = Γ
-- subCtx {n} {Γ'} {T} (ConsCtx {n} {Γ1} {Γ2} (step pA) A) (Before {Γ'} {Γ} {n} {T} {pT} i) v
  -- = ConsCtx {n} {subCtx {n} {Γ'} {T} Γ i v} same (subType Γ i {!   !} v)
subCtx = {!   !}
-- TODO: big prob: definition of subCtx needs to depend on subType, because currently it just always returns empty ctx.
-- THE BIG Q: will this be possible to type check in Agda?

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
