open import Data.Nat

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
  Pi : ∀ {n m Γ} → (A : Type {n} Γ) → (B : Type {m} (ConsCtx {n} {Γ} {Γ} same A)) → Type {max n m} Γ
  fromValue : ∀ {n Γ} → Value {suc n} Γ (U {n}) → Type {n} Γ


data InCtx where
  End : ∀ {Γ' n} → {T : Type {n} Γ'} → InCtx {n} (ConsCtx same T) {Γ'} T
  Before : ∀ {Γ' Γ n} → {T : Type {n} Γ'} → {p : Γ' prefix Γ} → InCtx Γ T → InCtx (ConsCtx {n} (step {n} {Γ'} {Γ} {T} p) T) T


data Value where
  Lambda : ∀ {n Γ A B} → Value {n} (ConsCtx {n} same A) B → Value Γ (Pi A B)
  fromU : ∀ {n Γ T} → UnApp {n} Γ T → Value {n} Γ T
  fromType : ∀ {n Γ} → Type {n} Γ → Value {suc n} Γ (U {n})

subType : ∀{m Γ} → {A : Type {m} Γ} →
  (v : Type {m} (ConsCtx {m} same A)) → (v₀ : Value Γ A) → Type {m} Γ
sub : ∀{m Γ} → {A : Type {m} Γ} → {B : Type {m} (ConsCtx same A)}
  (v : Value (ConsCtx {m} same A) B) → (v₀ : Value Γ A) → Value Γ (subType B v₀)

data UnApp where
  Var : ∀ {n Γ T} → InCtx {n} Γ T → UnApp Γ T
  -- TODO: replace m in A with n
  App : ∀ {m Γ} → {A : Type {m} Γ} → {B : Type {m} (ConsCtx same A)} → UnApp Γ (Pi A B) →
    (x : Value Γ A) → UnApp Γ (subType B x)

-- subType {m} {Γ} {A} U v₀ = U
-- subType {m} {Γ} {A} (Pi v v₁) v₀ = Pi (subType v v₀) (subType v₁ v₀)
-- subType {m} {Γ} {A} (fromValue x) v₀ = {!   !}
subType = {!   !}
sub v v₀ = {! v  !}

-- TODO: dont require m to be same for A and v

-- TODO: reffering to my latex writup, make the whole language in Agda!!!!!!!
