# Store Passing Trasformation in call-by-push-value
```agda
module Store-Passing where

open import Data.Nat
open import Data.Product

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; module ≡-Reasoning)
```

We will again need *function extensionality*.
```agda
postulate
  funext : {A B : Set} {f g : A → B} → ((a : A) → f a ≡ g a) → f ≡ g
```

We also recall a limited form of `CBPV`. This will be our target language for the translation.
Also, **note that we add a law, `bind-assoc`**.
```agda
record CBPV : Set₂ where
  field
    -- sorts
    ValType  : Set₁
    CompType : Set₁

  field
    -- value types
    U    : CompType → ValType
    ⊤    : ValType
    _⊗_  : ValType → ValType → ValType
    void : ValType
    _⊎_  : ValType → ValType → ValType

    -- computation types
    F    : ValType → CompType
    unit : CompType
    _cx_  : CompType → CompType → CompType
    _⇀_  : ValType → CompType → CompType

  infixr 5 _⊗_
  infixr 4 _cx_
  infixr 1 _⇀_

  field
    -- values vs. computations
    val  : ValType  → Set
    comp : CompType → Set

  -- value introductions
    susp : {X : CompType} → comp X → val (U X)
    ∗    : val ⊤
    _⊗,_ : {A B : ValType} → val A → val B → val (A ⊗ B)
    inj₁ : {A B : ValType} → val A → val (A ⊎ B)
    inj₂ : {A B : ValType} → val B → val (A ⊎ B)

    -- computation introductions
    ret : {A : ValType} → val A → comp (F A)
    triv : comp unit
    _c,_ : {X Y : CompType} → comp X → comp Y → comp (X cx Y)
    ƛ : {A : ValType} {X : CompType} → (val A → comp X) → comp (A ⇀ X)

    -- value eliminations
    force : {X : CompType} → val (U X) → comp X
    check : {X : CompType} → val ⊤ → comp X → comp X
    split : {A B : ValType} {X : CompType} → val (A ⊗ B) → (val A → val B → comp X) → comp X
    absurd : {X : CompType} → val void → comp X
    case : {A B : ValType} {X : CompType} → val (A ⊎ B) → (val A → comp X) → (val B → comp X) → comp X

    -- computation eliminations
    bind : {A : ValType} {X : CompType} → comp (F A) → (val A → comp X) → comp X
    proj₁ : {X Y : CompType} → comp (X cx Y) → comp X
    proj₂ : {X Y : CompType} → comp (X cx Y) → comp Y
    ap : {A : ValType} {X : CompType} → comp (A ⇀ X) → val A → comp X

  infixr 3 _⊗,_
  infixr 4 _c,_
  infix 5 ƛ
  syntax ƛ (λ x → e) = ƛ x ⇒ e

  field
    -- value β laws
    U-β : {X : CompType} {x : comp X} →
      force (susp x) ≡ x
    ⊤-β : {X : CompType} {x : comp X} →
      check ∗ x ≡ x
    ⊗-β : {A B : ValType} {X : CompType} {a : val A} {b : val B} {x : val A → val B → comp X} →
      split (a ⊗, b) x ≡ x a b

    -- computation β laws
    F-β : {A : ValType} {X : CompType} {a : val A} {x : val A → comp X} →
      bind (ret a) x ≡ x a
    ×-β₁ : {X Y : CompType} {x : comp X} {y : comp Y} →
      proj₁ (x c, y) ≡ x
    ×-β₂ : {X Y : CompType} {x : comp X} {y : comp Y} →
      proj₂ (x c, y) ≡ y
    ⇀-β : {A : ValType} {X : CompType} {x : val A → comp X} {a : val A} →
      ap (ƛ x) a ≡ x a

    -- value η laws
    U-η : {X : CompType} {v : val (U X)} →
      susp (force v) ≡ v
    ⊤-η : {X : CompType} {v : val ⊤} {x : val ⊤ → comp X} →
      check v (x ∗) ≡ x v
    ⊗-η : {A B : ValType} {X : CompType} {v : val (A ⊗ B)} {x : val (A ⊗ B) → comp X} →
      split v (λ a b → x (a ⊗, b)) ≡ x v

    -- computation η laws
    F-η : {A : ValType} {e : comp (F A)} →
      bind e ret ≡ e
    ×-η : {X Y : CompType} {e : comp (X cx Y)} →
      (proj₁ e c, proj₂ e) ≡ e
    ⇀-η : {A : ValType} {X : CompType} {e : comp (A ⇀ X)} →
      (ƛ a ⇒ ap e a) ≡ e
    -- extra laws
    bind-assoc : {A B : ValType} {X : CompType} {fa : comp (F A)} {fb : val A → comp (F B)} {x : val B → comp X} →
      bind (bind fa fb) x ≡ bind fa λ a → bind (fb a) x
    bind-split : {A B C : ValType} {X : CompType} {ab : val (A ⊗ B)} {c : val A → val B → comp (F C)} {x : val C → comp X} →
      bind (split ab c) x ≡ split ab λ a b → bind (c a b) x
    -- bind-ap : {A B : ValType} {X : CompType} {c : val A} {f : val A → comp (F B)} {x : val B → comp X} →
      -- bind (ap f c) x ≡ ap (λ c → bind f x) c
  variable
    A B C : ValType
    X Y Z : CompType
```

## The source language: Mutable State

We will be translating from a version of call by value with mutable state.
For simplicity, we will assume that there is a single global memory cell.
We extend the `CBPV` record with the effects `set[_]⨾_` and `get⨾_` and their corresponding equations:
```agda
record CBPV-State (𝕊 : Set) : Set₂ where
  field
    cbpv : CBPV
  open CBPV cbpv public

  field
    set[_]⨾_ : {X : CompType} → 𝕊 → comp X → comp X
    get⨾_ : {X : CompType} → (𝕊 → comp X) → comp X

    F-set : {n : 𝕊} {A : ValType} {X : CompType} {e : comp (F A)} {x : val A → comp X} →
      bind (set[ n ]⨾ e) x ≡ set[ n ]⨾ bind e x
    F-get : {n : 𝕊} {A : ValType} {X : CompType} {e : 𝕊 → comp (F A)} {x : val A → comp X} →
      bind (get⨾ e) x ≡ get⨾ λ n → bind (e n) x

    get-get : {X : CompType} {x : 𝕊 → 𝕊 → comp X} →
      (get⨾ λ n₁ → get⨾ λ n₂ → x n₁ n₂) ≡ (get⨾ λ n → x n n)
    get-set : {X : CompType} {x : comp X} →
      (get⨾ λ n → set[ n ]⨾ x) ≡ x
    set-get : {X : CompType} {n : 𝕊} {x : 𝕊 → comp X} →
      (set[ n ]⨾ get⨾ x) ≡ (set[ n ]⨾ x n)
    set-set : {X : CompType} {n : 𝕊} {n' : 𝕊} {x : comp X} →
      (set[ n ]⨾ set[ n' ]⨾ x) ≡ (set[ n' ]⨾ x)
```
Here, `𝕊` is a type representing the state.

### Store-Passing Transformation(Safety Goal):
```agda
module Compile (cbpv : CBPV) (𝕊 : CBPV.ValType cbpv) where
  open CBPV cbpv

  compile : CBPV-State (val 𝕊)
  compile = record {
    cbpv = record cbpv {
      comp = λ ctype → comp (𝕊 ⇀ ctype);
      F = λ x → F (x ⊗ 𝕊);
      U = λ x → U (𝕊 ⇀ x);
      ret = λ x → ƛ s ⇒ ret (x ⊗, s);
      triv = ƛ _ ⇒ triv;
      _c,_ = λ l r → ƛ s ⇒ (ap l s c, ap r s);
      ƛ = λ f → ƛ s ⇒ ƛ a ⇒ ap (f a) s;
      bind = λ cA fASX → ƛ s ⇒ bind (ap cA s) λ aoxs → split aoxs λ a → ap (fASX a);
      proj₁ = λ xandy → ƛ s ⇒ CBPV.proj₁ cbpv (ap xandy s);
      proj₂ = λ xandy → ƛ s ⇒ CBPV.proj₂ cbpv (ap xandy s);
      ap = λ f v → ƛ s ⇒ ap (ap f s) v;
      F-η = λ {_} {e} →
        let open ≡-Reasoning in
        begin
          ƛ z ⇒ bind (ap e z) (λ z₁ → split z₁ (λ z₂ → ap (ƛ z₃ ⇒ ret (z₂ ⊗, z₃))))
        ≡⟨ Eq.cong ƛ (funext λ z →
          Eq.cong (λ x → bind (ap e z) x) (funext (λ z₁ → 
            Eq.cong (λ x → split z₁ x) (funext (λ _ → funext (λ _ → ⇀-β))))
          )) ⟩
          ƛ z ⇒ bind (ap e z) (λ z₁ → split z₁ (λ z₂ z₃ → ret (z₂ ⊗, z₃)))
        ≡⟨ Eq.cong ƛ (funext λ z →
          Eq.cong (λ x → bind (ap e z) x) (funext (λ _ → 
            ⊗-η
          ))) ⟩
          ƛ z ⇒ bind (ap e z) ret
        ≡⟨ Eq.cong ƛ (funext (λ _ → F-η)) ⟩
          ƛ z ⇒ ap e z
        ≡⟨ ⇀-η ⟩
          e
        ∎;
      F-β = λ {_} {_} {a} {x} →
        let open ≡-Reasoning in
        begin
          ƛ z ⇒ bind ((ap (ƛ z₁ ⇒ ret (a ⊗, z₁))) z) (λ z₁ → split z₁ λ z₂ → ap (x z₂))
        ≡⟨ Eq.cong ƛ (funext λ z → Eq.cong (λ y → bind y (λ z₁ → split z₁ λ z₂ → ap (x z₂))) ⇀-β) ⟩
          ƛ z ⇒ bind (ret (a ⊗, z)) (λ z₁ → split z₁ (λ z₂ → ap (x z₂)))
        ≡⟨ Eq.cong ƛ (funext λ z → F-β) ⟩
          ƛ z ⇒ split (a ⊗, z) (λ z₂ → ap (x z₂))
        ≡⟨ Eq.cong ƛ (funext λ z → ⊗-β) ⟩
          ƛ z ⇒ (λ z₂ → ap (x z₂)) a z
        ≡⟨ Eq.cong ƛ Eq.refl ⟩
          ƛ ((λ z₂ → ap (x z₂)) a)
        ≡⟨⟩
          ƛ (ap (x a))
        ≡⟨ ⇀-η ⟩
          x a
        ∎;
      ×-η = λ {_ _} {e} →
        let open ≡-Reasoning in
        begin
          ƛ z ⇒ ((ap (ƛ z₁ ⇒ CBPV.proj₁ cbpv (ap e z₁)) z) c, (ap (ƛ z₁ ⇒ CBPV.proj₂ cbpv (ap e z₁)) z))
        ≡⟨ Eq.cong ƛ Eq.refl ⟩
          ƛ z ⇒ ((ap (ƛ z₁ ⇒ CBPV.proj₁ cbpv (ap e z₁)) z) c, (ap (ƛ z₁ ⇒ CBPV.proj₂ cbpv (ap e z₁)) z))
        ≡⟨ Eq.cong ƛ (funext (λ z → Eq.cong (λ x → x c, (ap (ƛ z₁ ⇒ CBPV.proj₂ cbpv (ap e z₁)) z)) ⇀-β)) ⟩
          ƛ z ⇒ ((CBPV.proj₁ cbpv (ap e z)) c, (ap (ƛ z₁ ⇒ CBPV.proj₂ cbpv (ap e z₁)) z))
        ≡⟨ Eq.cong ƛ (funext (λ z → Eq.cong (λ x → (CBPV.proj₁ cbpv (ap e z)) c, x) ⇀-β)) ⟩
          ƛ z ⇒ ((CBPV.proj₁ cbpv (ap e z)) c, (CBPV.proj₂ cbpv (ap e z)))
        ≡⟨ Eq.cong ƛ (funext (λ z → ×-η)) ⟩
          ƛ z ⇒ (ap e z)
        ≡⟨ ⇀-η ⟩
          e
        ∎;
      ×-β₁ = λ {_ _} {x} {y} →
        let open ≡-Reasoning in
        begin
          ƛ z ⇒ CBPV.proj₁ cbpv (ap (ƛ z₁ ⇒ (ap x z₁ c, ap y z₁)) z)
        ≡⟨ Eq.cong ƛ (funext λ z → Eq.cong (λ x₁ → CBPV.proj₁ cbpv x₁) ⇀-β) ⟩
          ƛ z ⇒ CBPV.proj₁ cbpv (ap x z c, ap y z)
        ≡⟨ Eq.cong ƛ (funext λ z → ×-β₁) ⟩
          ƛ z ⇒ ap x z
        ≡⟨ ⇀-η ⟩
          x
        ∎;
      ×-β₂ = λ {_ _} {x} {y} →
        let open ≡-Reasoning in
        begin
          ƛ z ⇒ CBPV.proj₂ cbpv (ap (ƛ z₁ ⇒ (ap x z₁ c, ap y z₁)) z)
        ≡⟨ Eq.cong ƛ (funext λ z → Eq.cong (λ x₁ → CBPV.proj₂ cbpv x₁) ⇀-β) ⟩
          ƛ z ⇒ CBPV.proj₂ cbpv (ap x z c, ap y z)
        ≡⟨ Eq.cong ƛ (funext λ z → ×-β₂) ⟩
          ƛ z ⇒ ap y z
        ≡⟨ ⇀-η ⟩
          y
        ∎;
      ⇀-β = λ {_} {_} {x} {a} →
        let open ≡-Reasoning in
        begin
          ƛ (λ z → ap (ap (ƛ (λ z₁ → ƛ (λ z₂ → ap (x z₂) z₁))) z) a)
        ≡⟨ Eq.cong ƛ (funext λ z → Eq.cong (λ x₁ → ap x₁ a) ⇀-β) ⟩
          ƛ (λ z → ap (ƛ (λ z₂ → ap (x z₂) z)) a)
        ≡⟨ Eq.cong ƛ (funext λ z → ⇀-β) ⟩
          ƛ (λ z → ap (x a) z)
        ≡⟨ ⇀-η ⟩
          x a
        ∎;
      ⇀-η = λ {_} {_} {e} →
        let open ≡-Reasoning in
        begin
          ƛ (λ z → ƛ (λ z₁ → ap (ƛ (λ z₂ → ap (ap e z₂) z₁)) z))
        ≡⟨ Eq.cong ƛ (funext λ z → Eq.cong ƛ (funext λ z₁ → ⇀-β)) ⟩
          ƛ (λ z → ƛ (λ z₁ → ap (ap e z) z₁))
        ≡⟨ Eq.cong ƛ (funext λ z → ⇀-η) ⟩
          ƛ (λ z → ap e z )
        ≡⟨ ⇀-η ⟩
          e
        ∎;
      bind-split = λ {_ _ _} {_} {ab} {c} {x} →
        let cfl : (ab : val (A ⊗ B)) → (Σ[ (a , b) ∈ (val A × val B) ] (ab ≡ (a ⊗, b)))
            cfl = {!   !}
            ((a , b) , pf) = cfl ab
        in
        let open ≡-Reasoning in
        begin
          ƛ z ⇒ bind (ap (split ab c) z) (λ z₁ → split z₁ (λ z₂ → ap (x z₂)))
        ≡⟨ Eq.cong ƛ (funext λ z → Eq.cong (λ x₁ → bind (ap (split x₁ c) z) (λ z₁ → split z₁ (λ z₂ → ap (x z₂)))) pf) ⟩
          ƛ z ⇒ bind (ap (split (a ⊗, b) c) z) (λ z₁ → split z₁ (λ z₂ → ap (x z₂)))
        ≡⟨ Eq.cong ƛ (funext λ z → Eq.cong (λ x₁ → bind (ap x₁ z) (λ z₁ → split z₁ (λ z₂ → ap (x z₂)))) ⊗-β) ⟩
          ƛ z ⇒ bind (ap (c a b) z) (λ z₁ → split z₁ (λ z₂ → ap (x z₂)))
        ≡⟨ Eq.sym ⊗-β ⟩
          split (a ⊗, b) (λ z z₁ → (ƛ z₂ ⇒ bind (ap (c z z₁) z₂) (λ z₃ → split z₃ (λ z₄ → ap (x z₄)))))
        ≡⟨ Eq.cong (λ x₁ → split x₁ λ z z₁ → (ƛ z₂ ⇒ bind (ap (c z z₁) z₂) (λ z₃ → split z₃ (λ z₄ → ap (x z₄))))) (Eq.sym pf) ⟩
          split ab (λ z z₁ → (ƛ z₂ ⇒ bind (ap (c z z₁) z₂) (λ z₃ → split z₃ (λ z₄ → ap (x z₄)))))
        ∎;
      bind-assoc = λ {_ _} {_} {fa} {fb} {x} →
        let open ≡-Reasoning in
        begin
          ƛ z ⇒ bind (ap (ƛ (λ z₁ → bind (ap fa z₁) (λ z₂ → split z₂ (λ z₃ → ap (fb z₃))))) z) (λ z₁ → split z₁ (λ z₂ → ap (x z₂)))
        ≡⟨ Eq.cong ƛ (funext λ z → Eq.cong (λ x₁ → bind x₁ λ z₁ → split z₁ λ z₂ → ap (x z₂)) ⇀-β)  ⟩
          ƛ z ⇒ bind (bind (ap fa z) (λ z₂ → split z₂ (λ z₃ → ap (fb z₃)))) (λ z₁ → split z₁ (λ z₂ → ap (x z₂)))
        ≡⟨ Eq.cong ƛ (funext λ z → bind-assoc) ⟩
          ƛ z ⇒ (bind (ap fa z) λ a → bind (split a (λ z₃ → ap (fb z₃))) (λ z₁ → split z₁ (λ z₂ → ap (x z₂))))
        ≡⟨ Eq.cong ƛ (funext λ z → Eq.cong (λ x₁ → bind (ap fa z) x₁) (funext λ a → bind-split)) ⟩
          ƛ z ⇒ bind (ap fa z) (λ z₁ → split z₁ (λ z₂ → (λ y → bind (ap (fb z₂) y) (λ z₄ → split z₄ (λ z₅ → ap (x z₅))))))
        ≡⟨ Eq.cong ƛ (funext λ z → Eq.cong (λ x₁ → bind (ap fa z) x₁) (funext λ z₁ → Eq.cong (λ x₁ → split z₁ x₁) (funext λ z₂ → funext λ y → Eq.sym ⇀-β))) ⟩
          ƛ z ⇒ bind (ap fa z) (λ z₁ → split z₁ (λ z₂ → (λ y → ap (ƛ (λ z₃ → bind (ap (fb z₂) z₃) (λ z₄ → split z₄ (λ z₅ → ap (x z₅))))) y)))
        ≡⟨ Eq.cong ƛ (funext λ z → Eq.cong (λ x₁ → bind (ap fa z) x₁) (funext λ a → Eq.refl)) ⟩
          ƛ z ⇒ bind (ap fa z) (λ z₁ → split z₁ (λ z₂ → ap (ƛ (λ z₃ → bind (ap (fb z₂) z₃) (λ z₄ → split z₄ (λ z₅ → ap (x z₅)))))))
        ∎;
      CompType = CompType; --Just explicitly showing that these are unchanged
      ValType = ValType
    };
      -- set[_]⨾_ : {X : CompType} → 𝕊 → comp X → comp X = ?;
    set[_]⨾_ = λ x lvalue → ƛ _ ⇒ ap lvalue x;
      -- get⨾_ : {X : CompType} → (𝕊 → comp X) → comp X
    get⨾_ = λ user → ƛ s ⇒ ap (user s) s;

      -- F-set : {n : 𝕊} {A : ValType} {X : CompType} {e : comp (F A)} {x : val A → comp X} →
      --   bind (set[ n ]⨾ e) x ≡ set[ n ]⨾ bind e x
    F-set = λ {n} {_} {_} {e} {x} →
        let open ≡-Reasoning in
        begin
          ƛ z ⇒ bind (ap (ƛ _ ⇒ ap e n) z) (λ z₁ → split z₁ (λ z₂ → ap (x z₂)))
        ≡⟨ Eq.cong ƛ (funext λ _ → Eq.cong (λ x₁ → bind x₁ (λ z₁ → split z₁ (λ z₂ → ap (x z₂)))) ⇀-β) ⟩
          ƛ _ ⇒ bind (ap e n) (λ z₁ → split z₁ (λ z₂ → ap (x z₂)))
        ≡⟨ Eq.cong ƛ (funext λ _ → Eq.sym ⇀-β) ⟩
          ƛ _ ⇒ (ap (ƛ z ⇒ bind (ap e z) (λ z₁ → split z₁ (λ z₂ → ap (x z₂)))) n)
        ∎;
      -- F-get : {n : 𝕊} {A : ValType} {X : CompType} {e : 𝕊 → comp (F A)} {x : val A → comp X} →
      --   bind (get⨾ e) x ≡ get⨾ λ n → bind (e n) x
    F-get = λ {n} {_} {_} {e} {x} →
        let open ≡-Reasoning in
        begin
          ƛ z ⇒ bind (ap (ƛ z₁ ⇒ ap (e z₁) z₁) z) (λ z₁ → split z₁ (λ z₂ → ap (x z₂)))
        ≡⟨ Eq.cong ƛ (funext λ z → Eq.cong (λ x₁ → bind x₁ (λ z₁ → split z₁ (λ z₂ → ap (x z₂))) ) ⇀-β ) ⟩
          ƛ z ⇒ bind (ap (e z) z) (λ z₁ → split z₁ (λ z₂ → ap (x z₂)))
        ≡⟨ Eq.cong ƛ (funext λ z → Eq.sym ⇀-β) ⟩
          ƛ z ⇒ (ap (ƛ z₁ ⇒ bind (ap (e z) z₁) (λ z₂ → split z₂ (λ z₃ → ap (x z₃)))) z)
        ∎;

      -- get-get : {X : CompType} {x : 𝕊 → 𝕊 → comp X} →
      --   (get⨾ λ n₁ → get⨾ λ n₂ → x n₁ n₂) ≡ (get⨾ λ n → x n n)
    get-get = λ {_} {x} →
        let open ≡-Reasoning in
        begin
          ƛ (λ z → ap (ƛ (λ z₁ → ap (x z z₁) z₁)) z)
        ≡⟨ Eq.cong ƛ (funext λ z → ⇀-β) ⟩
          ƛ (λ z → ap (x z z) z)
        ∎;
      -- get-set : {X : CompType} {x : comp X} →
      --   (get⨾ λ n → set[ n ]⨾ x) ≡ x
    get-set = λ {_} {x} →
        let open ≡-Reasoning in
        begin
          ƛ (λ z → ap (ƛ (λ _ → ap x z)) z)
        ≡⟨ Eq.cong ƛ (funext λ z → ⇀-β) ⟩
          ƛ (λ z → ap x z)
        ≡⟨ ⇀-η ⟩
          x
        ∎;
      -- set-get : {X : CompType} {n : 𝕊} {x : 𝕊 → comp X} →
      --   (set[ n ]⨾ get⨾ x) ≡ (set[ n ]⨾ x n)
    set-get = λ {_} {n} {x} →
        let open ≡-Reasoning in
        begin
          ƛ (λ _ → ap (ƛ (λ z → ap (x z) z)) n)
        ≡⟨ Eq.cong ƛ (funext λ _ → ⇀-β) ⟩
          ƛ (λ _ → ap (x n) n)
        ∎;
      -- set-set : {X : CompType} {n : 𝕊} {n' : 𝕊} {x : comp X} →
      --   (set[ n ]⨾ set[ n' ]⨾ x) ≡ (set[ n' ]⨾ x)
    set-set = λ {_} {n} {n'} {x} →
        let open ≡-Reasoning in
        begin
          ƛ (λ _ → ap (ƛ (λ _ → ap x n')) n)
        ≡⟨ Eq.cong ƛ (funext λ _ → ⇀-β) ⟩
          ƛ (λ _ → ap x n')
        ∎
    }
```

### Isomorphism between the two forms (Target Goal):
Currently work in progress. I have some weird error where it thinks these shuld be of type CBPV.

But I think that CBPV is a module not a type, so I am confused.
```human
record _↔_ (𝔸 𝔹 : Set) : Set where
  field
    to : 𝔸 → 𝔹
    from : 𝔹 → 𝔸
    to-from : (𝕒 : 𝔸) → from (to 𝕒) ≡ 𝕒
    from-to : (𝕓 : 𝔹) → to (from 𝕓) ≡ 𝕓

variable 𝕊 : Set
module Transformation (cbpvs : CBPV-State 𝕊) where
  open CBPV-State cbpvs

  store-passing : ((CBPV.comp (CBPV.F CBPV.⊤) × 𝕊) ↔ comp (F ⊤))
  _↔_.to store-passing f ={! !} 
  _↔_.from store-passing x = {!   !}
  _↔_.to-from store-passing f = {!   !}
  _↔_.from-to store-passing f = {!   !}
```

### Test Cases Straight from PSet9:
This should all be still working with no unfinished goals just to make sure that our new definitions haven't broken any obvious proofs.

First, we implement an imperative factorial algorithm using mutable state, where the state is a single natural number.
```agda
module Factorial (cbpv : CBPV-State ℕ) where
  open CBPV-State cbpv

  fact : ℕ → comp (F ⊤)
  fact zero = set[ 1 ]⨾ (ret ∗)
  fact (suc n) =
    bind (fact n) λ _ →
    get⨾ λ res →
    set[ (suc n * res) ]⨾
    ret ∗
```

Of course, we can also implement a functional specification, `spec`, for factorial:
```agda
  spec : ℕ → ℕ
  spec zero = 1
  spec (suc n) = suc n * spec n
```

Prove that `fact` matches the specification.
```agda
  correctness : (n : ℕ) → fact n ≡ set[ spec n ]⨾ ret ∗
  correctness zero = Eq.refl
  correctness (suc n) =
    let open ≡-Reasoning in
    begin
      fact (suc n)
    ≡⟨⟩
      ( bind (fact n) λ _ →
        get⨾ λ res →
        set[ (suc n * res) ]⨾
        ret ∗
      )
    ≡⟨ Eq.cong (λ x → bind x (λ _ → get⨾ λ res → set[ (suc n * res) ]⨾ ret ∗)) (correctness n) ⟩
      ( bind (set[ spec n ]⨾ ret ∗) λ _ →
        get⨾ λ res →
        set[ (suc n * res) ]⨾
        ret ∗
      )
    ≡⟨ F-set ⟩
      set[ spec n ]⨾ (bind (ret ∗) λ _ →
        get⨾ λ res →
        set[ (suc n * res) ]⨾
        ret ∗
      )
    ≡⟨ Eq.cong (λ x → set[ spec (n) ]⨾ x) F-β ⟩
      set[ spec n ]⨾ ((λ _ →
        get⨾ λ res →
        set[ (suc n * res) ]⨾
        ret ∗
      ) ∗ )
    ≡⟨⟩
      set[ spec n ]⨾ (
        get⨾ λ res →
        set[ (suc n * res) ]⨾
        ret ∗
      )
    ≡⟨ set-get ⟩
      set[ spec n ]⨾ (
        λ res →
        set[ (suc n * res) ]⨾
        ret ∗
      ) (spec n)
    ≡⟨⟩
      set[ spec n ]⨾ (
        set[ (suc n * (spec n)) ]⨾
        ret ∗
      ) 
    ≡⟨ set-set ⟩
      (set[ suc n * spec n ]⨾ ret ∗)
    ≡⟨⟩
      (set[ spec (suc n) ]⨾ ret ∗)
    ∎
```

Similarly, we may implement a function to compute the `n`th Fibonacci number.

Implement an imperative (i.e., stateful) algorithm `fib` to compute the `n`th Fibonacci number, and prove that it matches the specification.
```agda
module Fibonacci (cbpv : CBPV-State (ℕ × ℕ)) where
  open CBPV-State cbpv

  fib : ℕ → comp (F ⊤)
  fib zero = (set[ zero , suc zero ]⨾ (ret ∗))
  fib (suc n) = bind (fib n) (λ _ → get⨾ λ ( x , y ) → set[ y , x + y ]⨾ (ret ∗))

  spec : ℕ → ℕ
  spec zero = 0
  spec (suc zero) = 1
  spec (suc (suc n)) = spec n + spec (suc n)

  correctness : (n : ℕ) → fib n ≡ set[ (spec n , spec (suc n)) ]⨾ ret ∗
  correctness zero = Eq.refl
  correctness (suc zero) =
    let open ≡-Reasoning in
    begin
      fib (suc zero)
    ≡⟨⟩
      bind (fib zero) (λ _ → get⨾ λ ( x , y ) → set[ y , x + y ]⨾ (ret ∗))
    ≡⟨ Eq.cong (λ x → bind x (λ _ → get⨾ λ ( x , y ) → set[ y , x + y ]⨾ (ret ∗))) (correctness zero) ⟩
      bind (set[ zero , suc zero ]⨾ ret ∗) (λ _ → get⨾ λ ( x , y ) → set[ y , x + y ]⨾ (ret ∗))
    ≡⟨ F-set ⟩
      set[ zero , suc zero ]⨾ (bind (ret ∗) (λ _ → get⨾ λ ( x , y ) → set[ y , x + y ]⨾ (ret ∗)))
    ≡⟨ Eq.cong (λ x → set[ zero , suc zero ]⨾ x) F-β ⟩
      set[ zero , suc zero ]⨾ (get⨾ λ ( x , y ) → set[ y , x + y ]⨾ (ret ∗))
    ≡⟨ set-get ⟩
      set[ zero , suc zero ]⨾ (set[ suc zero , zero + suc zero ]⨾ (ret ∗))
    ≡⟨ set-set ⟩
      set[ suc zero , zero + suc zero ]⨾ (ret ∗)
    ≡⟨ Eq.cong (λ x → set[ 1 , x ]⨾ (ret ∗)) Eq.refl ⟩
      ( set[ 1 , 1 ]⨾
        ret ∗
      )
    ∎
  correctness (suc (suc n)) =
    let open ≡-Reasoning in
    begin
      fib (suc (suc n))
    ≡⟨⟩
      bind (fib (suc n)) (λ _ → get⨾ λ ( x , y ) → set[ y , x + y ]⨾ (ret ∗))
    ≡⟨ Eq.cong (λ x → bind x (λ _ → get⨾ λ ( x , y ) → set[ y , x + y ]⨾ (ret ∗))) (correctness (suc n))  ⟩
      bind (set[ spec (suc n) , spec (suc (suc n)) ]⨾ ret ∗) (λ _ → get⨾ λ ( x , y ) → set[ y , x + y ]⨾ (ret ∗))
    ≡⟨ F-set ⟩
      set[ spec (suc n) , spec (suc (suc n)) ]⨾ (bind (ret ∗) (λ _ → get⨾ λ ( x , y ) → set[ y , x + y ]⨾ (ret ∗)))
    ≡⟨ Eq.cong (λ x → set[ spec (suc n) , spec (suc (suc n)) ]⨾ x) F-β ⟩
      set[ spec (suc n) , spec (suc (suc n)) ]⨾ (get⨾ λ ( x , y ) → set[ y , x + y ]⨾ (ret ∗))
    ≡⟨ set-get ⟩
      set[ spec (suc n) , spec (suc (suc n)) ]⨾ (set[ spec (suc (suc n)) , spec (suc n) + spec (suc (suc n)) ]⨾ (ret ∗))
    ≡⟨ set-set ⟩
      set[ spec (suc (suc n)) , spec (suc n) + spec (suc (suc n)) ]⨾ (ret ∗)
    ≡⟨ Eq.cong (λ x → set[ spec (suc (suc n)) , x ]⨾ (ret ∗)) Eq.refl ⟩
      ( set[ (spec (suc (suc n)) , spec (suc (suc (suc n)))) ]⨾
        ret ∗
      )
    ∎
```

Now, we consider mutable state more generally, for an arbitrary state type `𝕊`.
We define an inductive type `Effects` representing a finite sequence of `GET`/`SET` effects terminated by a `RET`:
```agda
module CanonicalForm {𝕊 : Set} (cbpv : CBPV-State 𝕊) where
  open CBPV-State cbpv

  data Effects : Set where
    RET : Effects
    SET : 𝕊 → Effects → Effects
    GET : (𝕊 → Effects) → Effects
```

We may then reify a sequence of effs as a computation of type `F ⊤`:
```agda
  reify : Effects → comp (F ⊤)
  reify RET = ret ∗
  reify (SET s effs) = set[ s ]⨾ reify effs
  reify (GET effs) = get⨾ λ s → reify (effs s)
```

In fact, using the laws for state, we can prove that every sequence of `get` and `set` effects has a canonical form:
> `get⨾ λ s → set[ (f s) ]⨾ (ret ∗)`
where `f : 𝕊 → 𝕊` is a pure function.
In other words, after canceling out redundant instructions, every computation will look like a `get` followed by a `set` (followed by `ret ∗`).

Prove this theorem (by induction on `effs`, the sequence of effects).
```agda
  thm : (effs : Effects) → Σ[ f ∈ (𝕊 → 𝕊) ] reify effs ≡ (get⨾ λ s → set[ (f s) ]⨾ (ret ∗))
  thm RET = (λ x → x) ,
    let open ≡-Reasoning in
    begin
      reify RET
    ≡⟨⟩
      ret ∗
    ≡⟨ Eq.sym get-set ⟩
      (get⨾ λ s → set[ s ]⨾ (ret ∗))
    ≡⟨⟩
      (get⨾ λ s → set[ ((λ x → x) s) ]⨾ (ret ∗))
    ∎
  thm (SET s effs) = 
    let g , ih = thm effs
    in
    (λ _ → g s) ,
    let open ≡-Reasoning in
    begin
      reify (SET s effs)
    ≡⟨⟩
      set[ s ]⨾ reify effs
    ≡⟨ Eq.cong (λ x → set[ s ]⨾ x) ih ⟩
      set[ s ]⨾ (get⨾ λ s → set[ g s ]⨾ (ret ∗))
    ≡⟨ set-get ⟩
      set[ s ]⨾ (set[ g s ]⨾ (ret ∗))
    ≡⟨ set-set ⟩
      set[ g s ]⨾ (ret ∗)
    ≡⟨ Eq.sym get-set ⟩
      (get⨾ λ unused → set[ unused ]⨾ (set[ g s ]⨾ (ret ∗)))
    ≡⟨ Eq.cong (λ x → get⨾ x) (funext (λ unused → set-set)) ⟩
      (get⨾ λ unused → set[ g s ]⨾ (ret ∗))
    ≡⟨⟩
      (get⨾ λ unused → set[ (λ _ →  g s) unused ]⨾ (ret ∗))
    ∎
  thm (GET effs) = 
    ( (λ x → Σ.proj₁ (thm (effs x)) x ),
    let open ≡-Reasoning in
    begin
      reify (GET effs)
    ≡⟨⟩
      (get⨾ λ s → reify (effs s))
    ≡⟨ Eq.cong (λ x → get⨾ x) (funext λ s → Σ.proj₂ (thm (effs s))  ) ⟩
      (get⨾ λ s → get⨾ λ r → set[ (Σ.proj₁ (thm (effs s))) r ]⨾ (ret ∗))
    ≡⟨ get-get ⟩
      (get⨾ λ s → set[ (Σ.proj₁ (thm (effs s))) s ]⨾ (ret ∗))
    ∎
    )
```
          