module lemma2 where

open import DSt2
open import CPSt2

open import Data.Nat
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Empty
open import Data.Product
open import Function
open import Relation.Nullary
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality


subst-cont  : {var : cpstyp → Set}{τ₁ τ₂ : typ}{μα : trail}{τ₃ : cpstyp} →
              (k₁ : var τ₃ → cpsvalue[ var ] (cpsT τ₁) →
               cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT τ₂)) →
              (v : cpsvalue[ var ] τ₃) →
              (k₂ : cpsvalue[ var ] (cpsT τ₁) →
               cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT τ₂)) → Set

subst-cont {var} {τ₁} {τ₂} {μα} {τ₃} k₁ v k₂ =
  {v₁ : var τ₃ → cpsvalue[ var ] (cpsT τ₁)} →
  {v₁′ : cpsvalue[ var ] (cpsT τ₁)} →
  --{t : var τ₃ → cpsvalue[ var ] (cpsM μα)} →
  {t′ : cpsvalue[ var ] (cpsM μα)} →
  cpsSubstVal (λ x → v₁ x) v v₁′ →
  --cpsSubstVal (λ x → t x) v t′ →
  cpsSubst (λ x → k₁ x (v₁ x) (t′)) v (k₂ v₁′ t′)

subst-cont′  : {var : cpstyp → Set}{τ₁ τ₂ : typ}{μα : trail}{τ₃ : cpstyp} →
              (k₁ : var τ₃ → cpsvalue[ var ] (cpsT τ₁) →
               cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT τ₂)) →
              (v : cpsvalue[ var ] τ₃) →
              (k₂ : cpsvalue[ var ] (cpsT τ₁) →
               cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT τ₂)) → Set

subst-cont′ {var} {τ₁} {τ₂} {μα} {τ₃} k₁ v k₂ =
  --{v₁ : var τ₃ → cpsvalue[ var ] (cpsT τ₁)} →
  {v₁′ : cpsvalue[ var ] (cpsT τ₁)} →
  --{t : var τ₃ → cpsvalue[ var ] (cpsM μα)} →
  {t′ : cpsvalue[ var ] (cpsM μα)} →
  --cpsSubstVal (λ x → v₁ x) v v₁′ →
  --cpsSubstVal (λ x → t x) v t′ →
  cpsSubst (λ x → k₁ x v₁′ (t′)) v (k₂ v₁′ t′)


-- subst-trail  : {var : cpstyp → Set}{τ₁ τ₂ : typ}{μα : trail}{τ₃ : cpstyp} →
--               (t₁ : var τ₃ → cpsvalue[ var ] (cpsM μα)) →
--               (v : cpsvalue[ var ] τ₃) →
--               (t₂ : cpsvalue[ var ] (cpsM μα)) → Set

-- subst-trail {var} {τ₁} {τ₂} {∙} {τ₃} t₁ v t₂ = cpsSubst (λ x → CPSVal CPSId) v (CPSVal CPSId)
-- subst-trail {var} {τ₁} {τ₂} {x ⇒ x₁ , μα} {τ₃} t₁ v t₂ = {!!}
  -- {k : var τ₃ → cpsvalue[ var ] (cpsT τ₁) →
  --              cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT τ₂)} →
  -- {k′ : cpsvalue[ var ] (cpsT τ₁) →
  --              cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT τ₂)} →
  -- {v₁ : var τ₃ → cpsvalue[ var ] (cpsT τ₁)} →
  -- {v₁′ : cpsvalue[ var ] (cpsT τ₁)} →
  -- cpsSubst (λ x → k x v₁′ t₂) v (k′ v₁′ t₂) →
  -- cpsSubstVal (λ x → v₁ x) v v₁′ →
  -- cpsSubst (λ x → k′ v₁′ (t₁ x)) v (k′ v₁′ t₂)

mutual
  SubstV≠ : {var : cpstyp → Set}{τ₁ τ₂ : cpstyp} →
            {t : cpsvalue[ var ] τ₁} →
            {v : cpsvalue[ var ] τ₂} →
            cpsSubstVal (λ y → t) v t

  SubstV≠ {var} {t = CPSVar x} = sVar≠
  SubstV≠ {var} {t = CPSNum n} = sNum
  SubstV≠ {var} {t = CPSFun e} = sFun λ x → Subst≠
  SubstV≠ {var} {t = CPSId} = sId
  SubstV≠ {t = CPSAppend x t t₁} = sApd SubstV≠ SubstV≠
  SubstV≠ {t = CPSCons x t t₁} = sCon SubstV≠ SubstV≠

  Subst≠  : {var : cpstyp → Set}{τ₁ τ₂ : cpstyp} →
            {t : cpsterm[ var ] τ₁} →
            {v : cpsvalue[ var ] τ₂} →
            cpsSubst (λ y → t) v t

  Subst≠ {t = CPSVal x} = sVal SubstV≠
  Subst≠ {t = CPSApp t t₁} = sApp Subst≠ Subst≠
  Subst≠ {t = CPSLet t x} = sLet (λ y → Subst≠) (λ y₂ → Subst≠)
  Subst≠ {t = CPSPlus t t₁} = sPlu Subst≠ Subst≠
  Subst≠ {t = CPSIdk x x₁ t} = sIdk SubstV≠ SubstV≠
  

mutual

  SubstV-id  : {var : typ → Set}{τ₁ τ₂ : typ} →
               {v₁ : value[ var ] τ₁} →
               {v : value[ var ] τ₂} →
                SubstVal (λ _ → v₁) v v₁

  SubstV-id {var} {τ₁} {τ₂} {Var x} {v} = sVar≠
  SubstV-id {var} {.Nat} {τ₂} {Num n} {v} = sNum
  SubstV-id {var} {.(_ ⇒ _ ⟨ _ ⟩ _ ⟨ _ ⟩ _)} {τ₂} {Fun e₁} {v} = sFun λ x → Subst-id


  Subst-id  : {var : typ → Set}{τ₁ τ₂ α β : typ}{μα μβ : trail} →
              {μs : trails[ μβ ] μα}{t : term[ var ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β} →
              {v : value[ var ] τ₂} →
                Subst (λ _ → t) v t

  Subst-id {var} {τ₁} {τ₂} {α} {.α} {μα} {.μα}  {t = Val x} {v} = sVal SubstV-id
  Subst-id {var} {τ₁} {τ₂} {α} {β} {μα} {μβ} {t = App t t₁} {v} = sApp Subst-id Subst-id
  Subst-id {var} {.Nat} {τ₂} {α} {β} {μα} {μβ} {t = Plus t t₁} {v} = sPlu Subst-id Subst-id
  Subst-id {var} {τ₁} {τ₂} {α} {β} {μα} {μβ} {t = Control x x₁ x₂ e} {v} = sCon (λ k → Subst-id)
  Subst-id {var} {τ₁} {τ₂} {α} {.α} {μα} {.μα}  {t = Prompt x t} {v} = sPro Subst-id

mutual
  eSubstV  : {var : cpstyp → Set} {τ₁ τ : typ} →
             {v₁ : var (cpsT τ) → value[ var ∘ cpsT ] τ₁} →
             {v₁′ : value[ var ∘ cpsT ] τ₁} →
             {v : value[ var ∘ cpsT ] τ} →
             SubstVal v₁ v v₁′ →
             cpsSubstVal (λ y → cpsV {var = var} (v₁ y)) (cpsV v) (cpsV v₁′)
             
  eSubstV SubstVal.sVar= = cpsSubstVal.sVar=
  eSubstV SubstVal.sVar≠ = cpsSubstVal.sVar≠
  eSubstV SubstVal.sNum = cpsSubstVal.sNum
  eSubstV (sFun sub) = sFun (λ x → sVal (sFun (λ x₁ → sVal (sFun (λ x₂ → eSubst (sub x) (λ x₃ → sApp (sApp Subst≠ (sVal x₃)) Subst≠))))))

  eSubst   : {var : cpstyp → Set} {τ₁ α β τ : typ} {μα μβ : trail}{μs : trails[ μβ ] μα} →
             {e₁ : var (cpsT τ) →
               term[ var ∘ cpsT ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β} →
             {e₂ : term[ var ∘ cpsT ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β} →
             {v : value[ var ∘ cpsT ] τ} →
             {k : cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsMs μs) → cpsterm[ var ] (cpsT α)} →
             {t :  cpsvalue[ var ] cpsM μβ} →
             --{sub : subst-cont′ (λ x → k) (cpsV v) k} →
             --{trail : cpsvalue[ var ] cpsM μα} →
             Subst e₁ v e₂ →
             subst-cont (λ x → k) (cpsV v) k →
             cpsSubst (λ x → cpsTerm (e₁ x) k t) (cpsV v)
             (cpsTerm e₂ k t)
--eq eSubstV x
  eSubst (sVal x) eq = eq (eSubstV x)
  eSubst (sApp x x₂) eq = ekSubst x (λ x₁ → ekSubst x₂ (λ x₃ → sApp (sApp (sApp (sVal x₁) (sVal x₃)) Subst≠) Subst≠))
  eSubst (sPlu x x₂) eq = ekSubst x (λ x₁ → ekSubst x₂ (λ x₃ → sLet (λ x₄ → Subst≠) (λ x₄ → sPlu (sVal x₁) (sVal x₃))))
  eSubst (sCon x) eq = sLet (λ x₂ → eSubst (x x₂) (λ x₆ → sIdk x₆ SubstV≠)) (λ x₂ → Subst≠)
  eSubst (sPro x) eq = sLet (λ x₂ → Subst≠) λ x₄ → eSubst x (λ x₅ → sIdk x₅ SubstV≠)


  schematicV : {var : cpstyp → Set} {τ₁ α : typ}{μα : trail} →
             (k : cpsvalue[ var ] (cpsT τ₁) →
                  cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)) →
              Set
             
  schematicV {var} {τ₁} {μα = μα} k =
             (v : value[ var ∘ cpsT ] τ₁) →
             (t : cpsvalue[ var ] cpsM μα) →
             cpsSubst (λ x → k (CPSVar x) t) (cpsV v) (k (cpsV v) t)

  schematic  : {var : cpstyp → Set} {τ₁ α : typ}{μα : trail} →
               (k : cpsvalue[ var ] (cpsT τ₁) →
                    cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)) →
              Set
  schematic  {var} {τ₁} {μα = μα} k =
             (v : cpsvalue[ var ] (cpsT τ₁)) →
             (t : cpsvalue[ var ] cpsM μα) →
             cpsSubst (λ x → k (CPSVar x) t) v (k v t)

  schematicV′ : {var : cpstyp → Set} {τ₁ α : typ}{μα : trail} →
             (k : cpsvalue[ var ] (cpsT τ₁) →
                  cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)) →
              Set
             
  schematicV′ {var} {τ₁} {μα = μα} k =
             (t : cpsvalue[ var ] (cpsM μα)) →
             (v₂ : cpsvalue[ var ] cpsT τ₁) →
             cpsSubst (λ x → k v₂ (CPSVar x)) t (k v₂ t)

  schematicK  : {var : cpstyp → Set} {τ₁ α : typ}{μα : trail}{τ : cpstyp} →
               (k : cpsvalue[ var ] τ → cpsvalue[ var ] (cpsT τ₁) →
                    cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)) →
              Set
  schematicK  {var} {τ₁} {μα = μα}{τ = τ} k =
             {v : cpsvalue[ var ] τ} →
             (x : cpsvalue[ var ] (cpsT τ₁)) →
             (t : cpsvalue[ var ] cpsM μα) →
             cpsSubst (λ x₁ → k (CPSVar x₁) x t) v (k v x t)
             --cpsSubst (λ x → k (CPSVar x) t) v (k v t)
  schematicK′  : {var : cpstyp → Set} {τ₁ α : typ}{μα : trail}{τ : cpstyp} →
               (k : var τ → cpsvalue[ var ] (cpsT τ₁) →
                    cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)) →
              Set
  schematicK′  {var} {τ₁}{α} {μα = μα}{τ = τ} k =
             -- {m : var τ → cpsvalue[ var ] (cpsT τ₁)}→
             -- {x₁′ : cpsvalue[ var ] (cpsT τ₁)} →
             {v : var τ} →
             (x : cpsvalue[ var ] (cpsT τ₁)) →
             (t : cpsvalue[ var ] cpsM μα) →
             {k₂ : cpsvalue[ var ] (cpsT τ₁) →
                    cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)} →
             cpsSubst (λ x₁ → k x₁ x t) (CPSVar v) (k₂ x t)


  
  kSubst′′ : {var : cpstyp → Set}{τ₁ α β : typ} {μα μβ : trail}{μs : trails[ μβ ] μα} {τ : cpstyp} →
           (e : term[ var ∘ cpsT ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β) →
           {v : var τ} →
           (k₁ : var τ →
                  cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsMs μs) → cpsterm[ var ] (cpsT α)) →
           {k₂ : cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsMs μs) → cpsterm[ var ] (cpsT α)} →
           {t₁ : cpsvalue[ var ] (cpsM μβ)} →
           --{t′ : cpsvalue[ var ] (cpsM μα)} →
           subst-cont k₁ (CPSVar v) k₂ →
           --schematicK′ k₁ →
           cpsSubst (λ x → cpsTerm e (k₁ x) t₁) (CPSVar v) (cpsTerm e k₂ t₁)
  kSubst′′ (Val x₁) k₁ x = x SubstV≠
  kSubst′′ (App e e₁) k₁ x = kSubst′′ e
                                 (λ x₁ →
                                    λ v₁ →
                                      cpsTerm e₁
                                      (λ v₂ t₂ →
                                         CPSApp
                                         (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
                                          (CPSVal
                                           (CPSFun
                                            (λ v₃ →
                                               CPSVal (CPSFun (λ t'' → k₁ x₁ (CPSVar v₃) (CPSVar t'')))))))
                                         (CPSVal t₂)))
                                 (λ {v₁} x₁ → kSubst′′ e₁
                                                  (λ x₂ →
                                                     λ v₂ t₂ →
                                                       CPSApp
                                                       (CPSApp (CPSApp (CPSVal (v₁ x₂)) (CPSVal v₂))
                                                        (CPSVal
                                                         (CPSFun
                                                          (λ v₃ →
                                                             CPSVal (CPSFun (λ t'' → k₁ x₂ (CPSVar v₃) (CPSVar t'')))))))
                                                       (CPSVal t₂))
                                                  (λ x₂ → sApp (sApp (sApp (sVal x₁) (sVal x₂))
                                                  (sVal (sFun (λ x₃ → sVal (sFun (λ x₄ → x SubstV≠)))))) Subst≠))
  kSubst′′ (Plus e e₁) k₁ x = kSubst′′ e
                                  (λ x₁ →
                                     λ v₁ →
                                       cpsTerm e₁
                                       (λ v₂ t₂ →
                                          CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂))
                                          (λ v₃ → k₁ x₁ (CPSVar v₃) t₂)))
                                  (λ {v₁} x₁ → kSubst′′ e₁
                                                   (λ x₂ →
                                                      λ v₂ t₂ →
                                                        CPSLet (CPSPlus (CPSVal (v₁ x₂)) (CPSVal v₂))
                                                        (λ v₃ → k₁ x₂ (CPSVar v₃) t₂))
                                                   (λ x₂ → sLet (λ x₃ → x SubstV≠)
                                                   (λ x₃ → sPlu (sVal x₁) (sVal x₂))))
  kSubst′′ (Control x₁ x₂ x₃ e) k₁ x = sLet (λ x₄ → Subst≠) (λ x₄ → sVal (sFun (λ x₅ →
                                      sVal (sFun (λ x₆ → sVal (sFun (λ x₇ → sLet (λ x₈ → x SubstV≠)
                                      (λ x₈ → Subst≠))))))))
  kSubst′′ (Prompt x₁ e) k₁ x = sLet (λ x₂ → x SubstV≠) (λ x₂ → Subst≠)
    

  kSubst : {var : cpstyp → Set}{τ₁ α β : typ} {μα μβ : trail}{μs : trails[ μβ ] μα} {τ : cpstyp} →
           (e : term[ var ∘ cpsT ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β) →
           {v : cpsvalue[ var ] τ} →
           (k₁ : cpsvalue[ var ] τ →
                  cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsMs μs) → cpsterm[ var ] (cpsT α)) →
           --{k₂ : cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)} →
           {t₁ : cpsvalue[ var ] (cpsM μβ)} →
           --{t′ : cpsvalue[ var ] (cpsM μα)} →
           --subst-cont k₁ v k₂ →
           schematicK k₁ →
           cpsSubst (λ x → cpsTerm e (k₁ (CPSVar x)) t₁) v (cpsTerm e (k₁ v) t₁)

  kSubst (Val x₁) k₁ {t₁ = t₁} sch = sch (cpsV x₁) t₁
  kSubst (App e e₁) k₁ sch = kSubst e
    (λ x →
       λ v₁ →
         cpsTerm e₁
         (λ v₂ t₂ →
            CPSApp
            (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
             (CPSVal
              (CPSFun
               (λ v₃ → CPSVal (CPSFun (λ t'' → k₁ x (CPSVar v₃) (CPSVar t'')))))))
            (CPSVal t₂)))
    (λ x t →
    kSubst e₁
      (λ x₁ →
         λ v₂ t₂ →
           CPSApp
           (CPSApp (CPSApp (CPSVal x) (CPSVal v₂))
            (CPSVal
             (CPSFun
              (λ v₃ →
                 CPSVal (CPSFun (λ t'' → k₁ x₁ (CPSVar v₃) (CPSVar t'')))))))
           (CPSVal t₂))
      (λ x₁ t₂ → sApp (sApp Subst≠ (sVal (sFun (λ x₂ → sVal (sFun (λ x₃ → sch (CPSVar x₂) (CPSVar x₃)))))))
      Subst≠))
  kSubst (Plus e e₁) k₁ sch = kSubst e
                                (λ x →
                                   λ v₁ →
                                     cpsTerm e₁
                                     (λ v₂ t₂ →
                                        CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂))
                                        (λ v₃ → k₁ x (CPSVar v₃) t₂)))
                                (λ x t →
                                kSubst e₁
                                  (λ x₁ →
                                     λ v₂ t₂ →
                                       CPSLet (CPSPlus (CPSVal x) (CPSVal v₂))
                                       (λ v₃ → k₁ x₁ (CPSVar v₃) t₂))
                                  (λ x₁ t₂ → sLet (λ x₂ → sch (CPSVar x₂) t₂)
                                  (λ x₂ → Subst≠)))
  kSubst (Control x₁ x₂ x₃ e) k₁ sch = sLet (λ x → Subst≠) (λ x → sVal (sFun
                                      (λ x₄ → sVal (sFun (λ x₅ → sVal (sFun (λ x₆ → sLet (λ x₇ →
                                      sch (CPSVar x₄) (CPSVar x₇)) (λ x₇ → Subst≠))))))))
  kSubst (Prompt x₁ e) k₁ {t₁ = t₁} sch = sLet (λ x → sch (CPSVar x) t₁) λ x → Subst≠

  tSubst : {var : cpstyp → Set}{τ₁ α β : typ} {μα μβ : trail}{μs : trails[ μβ ] μα} →
           (e : term[ var ∘ cpsT ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β) →
           {v : cpsvalue[ var ] (cpsM μβ)} →
           --(t₁ : var τ → cpsvalue[ var ] (cpsM μβ)) →
           {k : cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsMs μs) → cpsterm[ var ] (cpsT α)} →
           --(t₂ : cpsvalue[ var ] (cpsM μβ)) →
           --subst-trail {τ₁ = τ₁}{τ₂ = τ₂} t₁ v t₂ →
           schematicV′ k →
           cpsSubst (λ x → cpsTerm e k (CPSVar x)) v (cpsTerm e k v)

  tSubst (Val x) {v = v} sch = sch v (cpsV x)
  tSubst (App e e₁) sch = tSubst e (λ t v₂ → tSubst e₁ (λ t₁ v₃ → sApp Subst≠ (sVal sVar=)))
  tSubst (Plus e e₁) sch = tSubst e (λ t v₂ → tSubst e₁ (λ t₁ v₃ → sLet (λ x → sch t₁ (CPSVar x)) (λ x → Subst≠)))
  tSubst (Control x x₁ x₂ e) sch = sLet (λ x₃ → Subst≠) (λ x₃ → sVal
                                   (sFun (λ x₄ → sVal (sFun (λ x₅ → sVal (sFun (λ x₆ →
                                   sLet (λ x₇ → Subst≠) λ x₇ → sVal (sApd sVar= SubstV≠))))))))
  tSubst (Prompt x e) {v = v} sch = sLet (λ x₁ → sch v (CPSVar x₁)) λ x₁ → Subst≠


  ekSubst  : {var : cpstyp → Set} {τ τ₁ α β : typ} {μα μβ : trail}{μs : trails[ μβ ] μα} →
             {e₁ : (var ∘ cpsT) τ → term[ var ∘ cpsT ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β} →
             {e₂ : term[ var ∘ cpsT ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β} →
             {v : value[ var ∘ cpsT ] τ} →
             {k₁ : var (cpsT τ) → cpsvalue[ var ] (cpsT τ₁) →
              cpsvalue[ var ] (cpsMs μs) → cpsterm[ var ] (cpsT α)} →
             {k₂ : cpsvalue[ var ] (cpsT τ₁) →
              cpsvalue[ var ] (cpsMs μs) → cpsterm[ var ] (cpsT α)} →
             {t₁ : cpsvalue[ var ] (cpsM μβ)} →
             Subst e₁ v e₂ →
             subst-cont k₁ (cpsV v) k₂ →
             cpsSubst (λ y → cpsTerm (e₁ y) (k₁ y) t₁) (cpsV v)
                     (cpsTerm e₂ k₂ t₁)

  ekSubst (sVal x) eq = eq (eSubstV x)
  ekSubst (sApp sub₁ sub₂) eq = ekSubst sub₁ (λ m → ekSubst sub₂ (λ n → sApp (sApp (sApp (sVal m) (sVal n)) (sVal (sFun (λ x → sVal (sFun (λ x₁ → eq SubstV≠)))))) Subst≠))
  ekSubst (sPlu sub₁ sub₂) eq = ekSubst sub₁ (λ m → ekSubst sub₂ (λ n → sLet (λ x → eq SubstV≠) (λ x → sPlu (sVal m) (sVal n))))
  ekSubst (sCon e) eq = sLet (λ x → ekSubst (e x) (λ x₄ → sIdk x₄ SubstV≠)) λ x → sVal (sFun (λ x₄ → sVal (sFun λ x₁ → sVal (sFun (λ x₆ → sLet (λ x₇ → eq SubstV≠) (λ x₇ → Subst≠))))))
  ekSubst (sPro e) eq = sLet (λ v → eq SubstV≠) λ x₁ → ekSubst e (λ x₂ → sIdk x₂ SubstV≠)


-- ([e₁]′ @ k)[v/y] = [e₂]′ @ k
  -- ekSubst'  : {var : cpstyp → Set} {τ₁ τ α β : typ} {μα μβ : trail} →
  --             {e₁ : var (cpsT τ) →
  --                   term[ var ∘ cpsT ] τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β} →
  --             {e₂ : term[ var ∘ cpsT ] τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β} →
  --             {v : value[ var ∘ cpsT ] τ} →
  --             (k : cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsM μα) →
  --             cpsterm[ var ] (cpsT α)) →
  --             (t : cpsvalue[ var ] (cpsM μβ)) →
  --             Subst e₁ v e₂ →
  --             cpsSubst (λ x → cpsTerm (e₁ x) k t)
  --                     (cpsV v)
  --                     (cpsTerm e₂ k t)

  -- ekSubst' k t (sVal sub) = {!!}
  -- ekSubst' k t (sApp sub₁ sub₂) = {!!}
  -- ekSubst' k t (sPlu x x₁) = {!!}
  -- ekSubst' k t (sCon x) = {!!}
  -- ekSubst' k t (sPro x) = {!!}

  

-- schematic : {var : cpstyp → Set} {τ₁ α : typ}{μα : trail} →
--             (k : cpsvalue[ var ] (cpsT τ₁) →
--                  cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)) →
--             (t : cpsvalue[ var ] cpsM μα) → Set
-- schematic {var} {τ₁} k  t =
--   (v : cpsvalue[ var ] (cpsT τ₁)) →
--   cpsSubst (λ x → k (CPSVar x) t) v (k v t)

correctCont :  {var : cpstyp → Set} {τ₁ α β : typ} {μα μβ : trail}{μs : trails[ μβ ] μα} →
               (e : term[ var ∘ cpsT ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β) →
               (k₁ : cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsMs μs) → cpsterm[ var ] (cpsT α)) →
               {k₂ : cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsMs μs) → cpsterm[ var ] (cpsT α)} →
               {t₂ : cpsvalue[ var ] (cpsM μβ)} →
               schematic  k₁ →
               --schematicV  k₂ →
               -- ((v : value[ var ∘ cpsT ] τ₁) →
               --  subst-cont k₁ v k₂) →
               ((v : value[ var ∘ cpsT ] τ₁) → (t : cpsvalue[ var ] (cpsMs μs)) →
                cpsreduce (k₁ (cpsV v) t) (k₂ (cpsV v) t)) →
               cpsreduce (cpsTerm e k₁ t₂) (cpsTerm e k₂ t₂)

correctCont (Val x₁) k₁ {k₂} {t₂ = t₂} sch₁ x = x x₁ t₂
correctCont (App e e₁) k₁ {k₂}  {t₂} sch₁ x = begin
 (cpsTerm e
       (λ v₁ →
          cpsTerm e₁
          (λ v₂ t₃ →
             CPSApp
             (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
              (CPSVal
               (CPSFun
                (λ v → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v) (CPSVar t'')))))))
             (CPSVal t₃)))
       t₂)

  ⟶⟨ correctCont e
       (λ v₁ →
          cpsTerm e₁
          (λ v₂ t₃ →
             CPSApp
             (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
              (CPSVal
               (CPSFun
                (λ v → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v) (CPSVar t'')))))))
             (CPSVal t₃)))
       {λ v₁ →
          cpsTerm e₁
          (λ v₂ t₃ →
             CPSApp
             (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
              (CPSVal
               (CPSFun
                (λ v → CPSVal (CPSFun (λ t'' → k₂ (CPSVar v) (CPSVar t'')))))))
             (CPSVal t₃))}
       (λ v t → kSubst e₁
                    (λ x₁ →
                       λ v₂ t₃ →
                         CPSApp
                         (CPSApp (CPSApp (CPSVal x₁) (CPSVal v₂))
                          (CPSVal
                           (CPSFun
                            (λ v₁ → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v₁) (CPSVar t'')))))))
                         (CPSVal t₃))
                    (λ x₁ t₁ → sApp (sApp (sApp (sVal sVar=) Subst≠) Subst≠) Subst≠) )
                    (λ v t → correctCont e₁
                                 (λ v₂ t₃ →
                                    CPSApp
                                    (CPSApp (CPSApp (CPSVal (cpsV v)) (CPSVal v₂))
                                     (CPSVal
                                      (CPSFun
                                       (λ v₁ → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v₁) (CPSVar t'')))))))
                                    (CPSVal t₃))
                                 {λ v₂ t₃ →
                                    CPSApp
                                    (CPSApp (CPSApp (CPSVal (cpsV v)) (CPSVal v₂))
                                     (CPSVal
                                      (CPSFun
                                       (λ v₁ → CPSVal (CPSFun (λ t'' → k₂ (CPSVar v₁) (CPSVar t'')))))))
                                    (CPSVal t₃)}
                                 (λ v₁ t₁ → sApp (sApp (sApp Subst≠ (sVal sVar=)) Subst≠) Subst≠)
                                 (λ v₁ t₁ → rApp₁ (rApp₂ (rFun (λ x₁ → rFun (λ x₂ → x (Var x₁) (CPSVar x₂)))))))  ⟩

  (cpsTerm e
       (λ v₁ →
          cpsTerm e₁
          (λ v₂ t₃ →
             CPSApp
             (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
              (CPSVal
               (CPSFun
                (λ v → CPSVal (CPSFun (λ t'' → k₂ (CPSVar v) (CPSVar t'')))))))
             (CPSVal t₃)))
       t₂)

  ∎
correctCont (Plus e e₁) k₁ {k₂} {t₂ = t₂} sch₁ x = begin
  (cpsTerm e
       (λ v₁ →
          cpsTerm e₁
          (λ v₂ t₃ →
             CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂)) (λ v → k₁ (CPSVar v) t₃)))
       t₂)
  ⟶⟨ correctCont e
       (λ v₁ →
          cpsTerm e₁
          (λ v₂ t₃ →
             CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂)) (λ v → k₁ (CPSVar v) t₃)))
       {λ v₁ →
          cpsTerm e₁
          (λ v₂ t₃ →
             CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂)) (λ v → k₂ (CPSVar v) t₃))}
       (λ v t → kSubst e₁
                    (λ x₁ →
                       λ v₂ t₃ →
                         CPSLet (CPSPlus (CPSVal x₁) (CPSVal v₂))
                         (λ v₁ → k₁ (CPSVar v₁) t₃))
                    (λ x₁ t₁ → sLet (λ x₂ → Subst≠) (λ x₂ → sPlu
                    (sVal sVar=) Subst≠)))
       (λ v t → correctCont e₁
                    (λ v₂ t₃ →
                       CPSLet (CPSPlus (CPSVal (cpsV v)) (CPSVal v₂))
                       (λ v₁ → k₁ (CPSVar v₁) t₃))
                    {λ v₂ t₃ →
                       CPSLet (CPSPlus (CPSVal (cpsV v)) (CPSVal v₂))
                       (λ v₁ → k₂ (CPSVar v₁) t₃)}
                    (λ v₁ t₁ → sLet (λ x₁ → Subst≠)
                    (λ x₁ → sPlu Subst≠ (sVal sVar=)))
                    (λ v₁ t₁ → rLet₂ (λ x₁ → x (Var x₁) t₁))) ⟩
  (cpsTerm e
       (λ v₁ →
          cpsTerm e₁
          (λ v₂ t₃ →
             CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂)) (λ v → k₂ (CPSVar v) t₃)))
       t₂)
  ∎
correctCont {μs = μs} (Control{μs₁ = μs₁} x₁ x₂ x₃ e) k₁ {k₂} {t₂ = t₂} sch₁ x = begin
  (cpsTerm {μs = μs} (Control{μs₁ = μs₁} x₁ x₂ x₃ e) k₁ t₂)
  ⟶⟨ rLet₁ (rFun (λ x₄ → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ → x (Var x₄) (CPSVar x₇)))))) ⟩
  (cpsTerm {μs = μs} (Control{μs₁ = μs₁} x₁ x₂ x₃ e) k₂ t₂)
  ∎

correctCont (Prompt x₁ e) k₁ {k₂} {t₂ = t₂} sch₁ x = rLet₂ (λ x₂ → x (Var x₂) t₂)




mutual
  pSubstV≠ : {var : typ → Set} {τ₁ τ₂ : typ} →
             {t : value[ var ] τ₁ } →
             {v : value[ var ] τ₂ } →
             SubstVal (λ y → t) v t

  pSubstV≠ {t = Var x} = sVar≠
  pSubstV≠ {t = Num n} = sNum
  pSubstV≠ {t = Fun e₁} = sFun (λ x → pSubst≠)
  pSubst≠ : {var : typ → Set} {τ₁ τ₂ α β : typ}{μα μβ : trail}{μs : trails[ μβ ] μα} →
            {t : term[ var ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β} →
            {v : value[ var ] τ₂ } →
            Subst (λ y → t) v t

  pSubst≠ {t = Val x} = sVal pSubstV≠
  pSubst≠ {t = App t t₁} = sApp pSubst≠ pSubst≠
  pSubst≠ {t = Plus t t₁} = sPlu pSubst≠ pSubst≠
  pSubst≠ {t = Control x x₁ x₂ e} = sCon (λ k → pSubst≠)
  pSubst≠ {t = Prompt x t} = sPro pSubst≠

subst-context : {var : typ → Set} {τ α τ₁ τ₂ α' : typ}{μα μ₁ μ₂ : trail}{μt : trails[ μ₂ ] μ₁} →
                (con : pcontext[ var , τ ⟨ []{μα} ⟩ α ⟨ μα ⟩ α ] τ₁ ⟨ μt ⟩ τ₂ ⟨ μ₂ ⟩ α' ) →
                (v : value[ var ] τ) →
                Subst (λ x → pcontext-plug con (Val (Var x))) v
                      (pcontext-plug con (Val v))

subst-context Hole v = sVal sVar=
subst-context (Frame (App₁ e₂) con) v = sApp (subst-context con v) pSubst≠
subst-context (Frame (App₂ v₁) con) v = sApp pSubst≠ (subst-context con v)
subst-context (Frame (Plus₁ e₂) con) v = sPlu (subst-context con v) pSubst≠
subst-context (Frame (Plus₂ v₁) con) v = sPlu pSubst≠ (subst-context con v)





control-lemma : ∀ {var : cpstyp → Set}{τ τ₁ τ₂' τ₅ α β γ γ' t₁ t₂ : typ}
              {μ₀ μ₂ μ₁ μᵢ μα μβ μα' μγ : trail}
              --{μ[̇̇∙]α : trails[ ∙ ] μα}
              {μ[μ₂]μ₁ : trails[ μ₂ ] μ₁}→
              -- {μ[∙]μ₃ : trails[ ∙ ] μ₃} →
              {μ[β]μγ : trails[ μβ ] μγ} →
              {μ[α]μγ : trails[ μα ] μγ} →
              --{μ[α]μ₃ : trails[ μα ] μ₃} →  
              {μ[β]α : trails[ μβ ] μα} →
              {μ[∙]μᵢ : trails[ ∙ ] μᵢ} →
              (p₁ : pcontext[ var ∘ cpsT , τ ⟨ μ[β]α ⟩ α ⟨ μβ ⟩ β ]
                            τ₁ ⟨ μ[β]μγ ⟩ τ₅ ⟨ μβ ⟩ β ) →
              (p₂ : pcontext[ var ∘ cpsT , τ ⟨ []{μα'} ⟩ τ₂' ⟨ μα' ⟩ τ₂' ]
                            τ₁ ⟨ μ[α]μγ ⟩ τ₅ ⟨ μα ⟩ α ) →
              --{id₀ : is-id-trails τ₁ τ₅ μ[∙]μ₃} →
              (id : is-id-trails γ γ' μ[∙]μᵢ) →
              (c₁ : compatible (t₁ ⇒ t₂ , μ₁) μ₂ μ₀) →
              (c₂ : compatible μβ μ₀ μα) →
              same-pcontext p₁ p₂ →
              (e : var (cpsT (τ ⇒ t₁ ⟨ μ[μ₂]μ₁ ⟩ t₂ ⟨ μ₂ ⟩ α)) →
                   term[ var ∘ cpsT ] γ ⟨ μ[∙]μᵢ ⟩ γ' ⟨ ∙ ⟩ β) →
              (k₁ : cpsvalue[ var ] cpsT τ₁ → cpsvalue[ var ] cpsM μγ → cpsterm[ var ] cpsT τ₅) →
              (tr : cpsvalue[ var ] cpsM μβ) →
              (sch : schematic k₁) →
              (sch' : schematicV′ k₁) →
              cpsreduce
                (cpsTerm (pcontext-plug p₁ (Control{μs₁ = μ[μ₂]μ₁} id c₁ c₂ e)) k₁ tr)
                (cpsTerm{μs = μ[β]μγ}
                  (App{μ[γ]β = μ[β]α} (Val (Fun (λ x → pcontext-plug p₂ (Val (Var x)))))
                  (Control{μs₁ = μ[μ₂]μ₁} id c₁ c₂ e)) k₁ tr)



control-lemma = {!!}
  
{-
control-lemma Hole Hole id₁ c₁ c₂ x e k₁ tr sch sch' = begin
  (CPSLet
       (CPSVal
        (CPSFun
         (λ v →
            CPSVal
            (CPSFun
             (λ k' →
                CPSVal
                (CPSFun
                 (λ t' →
                    CPSLet
                    (CPSVal (CPSAppend c₂ tr (CPSCons c₁ (CPSVar k') (CPSVar t'))))
                    (λ t'' → k₁ (CPSVar v) (CPSVar t'')))))))))
       (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId))

  ⟵⟨ rLet₁ (rFun (λ x₁ → rFun (λ x₂ → rFun (λ x₃ → rLet₂ (λ x₄ → rBeta (sch' (CPSVar x₄) (CPSVar x₁))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend c₂ tr (CPSCons c₁ (CPSVar z₁) (CPSVar z₂))))
                 (λ z₃ →
                    CPSApp (CPSVal (CPSFun (λ z₄ → k₁ (CPSVar z) (CPSVar z₄))))
                    (CPSVal (CPSVar z₃))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x₁ → rFun (λ x₂ → rFun (λ x₃ → rLet₂ (λ x₄ → rApp₁ (rBeta
      (sVal (sFun (λ x₅ → sch (CPSVar x₁) (CPSVar x₅)))))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend c₂ tr (CPSCons c₁ (CPSVar z₁) (CPSVar z₂))))
                 (λ z₃ →
                    CPSApp
                    (CPSApp
                     (CPSVal
                      (CPSFun
                       (λ v₁ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₁) (CPSVar t'''))))))
                     (CPSVal (CPSVar z)))
                    (CPSVal (CPSVar z₃))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x₁ → rFun (λ x₂ → rFun (λ x₃ → rLet₂ (λ x₄ →
      rBeta (sApp Subst≠ (sVal sVar=))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend c₂ tr (CPSCons c₁ (CPSVar z₁) (CPSVar z₂))))
                 (λ z₃ →
                    CPSApp
                    (CPSVal
                     (CPSFun
                      (λ z₄ →
                         CPSApp
                         (CPSApp
                          (CPSVal
                           (CPSFun
                            (λ v₁ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₁) (CPSVar t'''))))))
                          (CPSVal (CPSVar z)))
                         (CPSVal (CPSVar z₄)))))
                    (CPSVal (CPSVar z₃))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x₁ → rFun (λ x₂ → rFun (λ x₃ → rLet₂ (λ x₄ → rApp₁ (rBeta
      (sVal (sFun (λ x₅ → sApp (sApp (sVal sVar=) Subst≠) Subst≠))))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend c₂ tr (CPSCons c₁ (CPSVar z₁) (CPSVar z₂))))
                 (λ z₃ →
                    CPSApp
                    (CPSApp
                     (CPSVal
                      (CPSFun
                       (λ z₄ →
                          CPSVal
                          (CPSFun
                           (λ z₅ →
                              CPSApp (CPSApp (CPSVal (CPSVar z₄)) (CPSVal (CPSVar z)))
                              (CPSVal (CPSVar z₅)))))))
                     (CPSVal
                      (CPSFun
                       (λ v₁ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₁) (CPSVar t''')))))))
                    (CPSVal (CPSVar z₃))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x₁ → rFun (λ x₂ → rFun (λ x₃ → rLet₂ (λ x₄ → rApp₁ (rApp₁ (rBeta
      (sVal (sFun (λ x₅ → sVal (sFun (λ x₆ → sApp (sApp Subst≠ (sVal sVar=)) Subst≠)))))))))))) ⟩
  (CPSLet
       (CPSVal
        (CPSFun
         (λ v →
            CPSVal
            (CPSFun
             (λ k' →
                CPSVal
                (CPSFun
                 (λ t' →
                    CPSLet
                    (CPSVal (CPSAppend c₂ tr (CPSCons c₁ (CPSVar k') (CPSVar t'))))
                    (λ t'' →
                       CPSApp
                       (CPSApp
                        (CPSApp
                         (CPSVal
                          (CPSFun
                           (λ x₁ →
                              CPSVal
                              (CPSFun
                               (λ k'' →
                                  CPSVal
                                  (CPSFun
                                   (λ t''' →
                                      CPSApp (CPSApp (CPSVal (CPSVar k'')) (CPSVal (CPSVar x₁)))
                                      (CPSVal (CPSVar t''')))))))))
                         (CPSVal (CPSVar v)))
                        (CPSVal
                         (CPSFun
                          (λ v₁ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₁) (CPSVar t''')))))))
                       (CPSVal (CPSVar t''))))))))))
       (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId))

  ∎


control-lemma
              (Frame (App₁ e₂) p₁') (Frame (App₁ .e₂) p₂') id₁ c₃ c₄
              (Frame {f₁ = (App₁ e₂)}{f₂ = (App₁ .e₂)} (App₁ .e₂) {c₁ = c₁}{c₂ = c₂} same) e k₁ t₁ sch sch' = begin

  (cpsTerm (pcontext-plug p₁' (Control id₁ c₃ c₄ e))
       (λ v₁ →
          cpsTerm e₂
          (λ v₂ t₄ →
             CPSApp
             (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
              (CPSVal
               (CPSFun
                (λ v → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v) (CPSVar t'')))))))
             (CPSVal t₄)))
       t₁)

  ⟶⟨ control-lemma  p₁' p₂' id₁ c₃ c₄ same e
       (λ v₁ →
          cpsTerm e₂
          (λ v₂ t₄ →
             CPSApp
             (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
              (CPSVal
               (CPSFun
                (λ v → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v) (CPSVar t'')))))))
             (CPSVal t₄)))
       t₁ (λ v t → kSubst e₂
                       (λ x →
                          λ v₂ t₄ →
                            CPSApp
                            (CPSApp (CPSApp (CPSVal x) (CPSVal v₂))
                             (CPSVal
                              (CPSFun
                               (λ v₁ → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v₁) (CPSVar t'')))))))
                            (CPSVal t₄))
                       (λ x t₄ → sApp (sApp (sApp (sVal sVar=) Subst≠) Subst≠) Subst≠))
                       (λ t v₂ → tSubst e₂ (λ t₄ v₃ → sApp Subst≠ (sVal sVar=))) ⟩
  cpsTerm {μs = {!!}}
    (App {μ[γ]β = {!!}} (Val (Fun (λ x → pcontext-plug p₂' (Val (Var x)))))
     (Control {μs₁ = {!!}} id₁ c₃ c₄ e))
    (λ v₁ →
       cpsTerm e₂
       (λ v₂ t₄ →
          CPSApp
          (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
           (CPSVal
            (CPSFun
             (λ v → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v) (CPSVar t'')))))))
          (CPSVal t₄)))
    t₁
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₁ → rFun (λ x₂ → rLet₂ (λ x₃ → rApp₁ (rApp₁ (rBeta
     (sVal (sFun (λ x₄ → sVal (sFun (λ x₅ → eSubst ((subst-context p₂' (Var x)))
     (λ x₆ → sApp (sApp Subst≠ (sVal x₆)) Subst≠))))))))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend c₄ t₁ (CPSCons c₃ (CPSVar z₁) (CPSVar z₂))))
                 (λ z₃ →
                    CPSApp
                    (CPSApp
                     (CPSVal
                      (CPSFun
                       (λ z₄ →
                          CPSVal
                          (CPSFun
                           (λ z₅ →
                              cpsTerm (pcontext-plug p₂' (Val (Var z)))
                              (λ v t'' →
                                 CPSApp (CPSApp (CPSVal (CPSVar z₄)) (CPSVal v)) (CPSVal t''))
                              (CPSVar z₅))))))
                     (CPSVal
                      (CPSFun
                       (λ v →
                          CPSVal
                          (CPSFun
                           (λ t'' →
                              cpsTerm e₂
                              (λ v₂ t₄ →
                                 CPSApp
                                 (CPSApp (CPSApp (CPSVal (CPSVar v)) (CPSVal v₂))
                                  (CPSVal
                                   (CPSFun
                                    (λ v₁ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₁) (CPSVar t''')))))))
                                 (CPSVal t₄))
                              (CPSVar t'')))))))
                    (CPSVal (CPSVar z₃))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId)
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₁ → rFun (λ x₂ → rLet₂ (λ x₃ →
      rApp₁ (rBeta (sVal (sFun (λ x₄ →
      kSubst (pcontext-plug p₂' (Val (Var x)))
        (λ y →
           λ v t'' → CPSApp (CPSApp (CPSVal y) (CPSVal v)) (CPSVal t''))
        (λ x₅ t → sApp (sApp (sVal sVar=) Subst≠) Subst≠)))))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend c₄ t₁ (CPSCons c₃ (CPSVar z₁) (CPSVar z₂))))
                 (λ z₃ →
                    CPSApp
                    (CPSVal
                     (CPSFun
                      (λ z₄ →
                         cpsTerm (pcontext-plug p₂' (Val (Var z)))
                         (λ v t'' →
                            CPSApp
                            (CPSApp
                             (CPSVal
                              (CPSFun
                               (λ v₁ →
                                  CPSVal
                                  (CPSFun
                                   (λ t''' →
                                      cpsTerm e₂
                                      (λ v₂ t₄ →
                                         CPSApp
                                         (CPSApp (CPSApp (CPSVal (CPSVar v₁)) (CPSVal v₂))
                                          (CPSVal
                                           (CPSFun
                                            (λ v₃ →
                                               CPSVal
                                               (CPSFun (λ t'''' → k₁ (CPSVar v₃) (CPSVar t'''')))))))
                                         (CPSVal t₄))
                                      (CPSVar t'''))))))
                             (CPSVal v))
                            (CPSVal t''))
                         (CPSVar z₄))))
                    (CPSVal (CPSVar z₃))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId)
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₁ → rFun (λ x₂ → rLet₂ (λ x₃ → rBeta
      (tSubst (pcontext-plug p₂' (Val (Var x)))
      (λ t v₂ → sApp (sApp Subst≠ Subst≠) (sVal sVar=)))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend c₄ t₁ (CPSCons c₃ (CPSVar z₁) (CPSVar z₂))))
                 (λ z₃ →
                    cpsTerm (pcontext-plug p₂' (Val (Var z)))
                    (λ v t'' →
                       CPSApp
                       (CPSApp
                        (CPSVal
                         (CPSFun
                          (λ v₁ →
                             CPSVal
                             (CPSFun
                              (λ t''' →
                                 cpsTerm e₂
                                 (λ v₂ t₄ →
                                    CPSApp
                                    (CPSApp (CPSApp (CPSVal (CPSVar v₁)) (CPSVal v₂))
                                     (CPSVal
                                      (CPSFun
                                       (λ v₃ →
                                          CPSVal (CPSFun (λ t'''' → k₁ (CPSVar v₃) (CPSVar t'''')))))))
                                    (CPSVal t₄))
                                 (CPSVar t'''))))))
                        (CPSVal v))
                       (CPSVal t''))
                    (CPSVar z₃)))))))))
    (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId)
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₁ → rFun (λ x₂ → rLet₂ (λ x₃ →
      correctCont (pcontext-plug p₂' (Val (Var x)))
        (λ v t'' →
           CPSApp
           (CPSApp
            (CPSVal
             (CPSFun
              (λ v₁ →
                 CPSVal
                 (CPSFun
                  (λ t''' →
                     cpsTerm e₂
                     (λ v₂ t₄ →
                        CPSApp
                        (CPSApp (CPSApp (CPSVal (CPSVar v₁)) (CPSVal v₂))
                         (CPSVal
                          (CPSFun
                           (λ v₃ →
                              CPSVal (CPSFun (λ t'''' → k₁ (CPSVar v₃) (CPSVar t'''')))))))
                        (CPSVal t₄))
                     (CPSVar t'''))))))
            (CPSVal v))
           (CPSVal t''))
        {k₂ =
         λ v t'' →
           CPSApp
           (CPSVal
            (CPSFun
             (λ t''' →
                cpsTerm e₂
                (λ v₂ t₄ →
                   CPSApp
                   (CPSApp (CPSApp (CPSVal v) (CPSVal v₂))
                    (CPSVal
                     (CPSFun
                      (λ v₃ →
                         CPSVal (CPSFun (λ t'''' → k₁ (CPSVar v₃) (CPSVar t'''')))))))
                   (CPSVal t₄))
                (CPSVar t'''))))
           (CPSVal t'')}
        (λ v t → sApp (sApp Subst≠ (sVal sVar=)) Subst≠)
        (λ v t → rApp₁ (rBeta (sVal (sFun (λ x₄ →
        kSubst e₂
          (λ y →
             λ v₂ t₄ →
               CPSApp
               (CPSApp (CPSApp (CPSVal y) (CPSVal v₂))
                (CPSVal
                 (CPSFun
                  (λ v₃ →
                     CPSVal (CPSFun (λ t'''' → k₁ (CPSVar v₃) (CPSVar t'''')))))))
               (CPSVal t₄))
          (λ x₅ t₄ → sApp (sApp (sApp (sVal sVar=) Subst≠) Subst≠) Subst≠))))))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend c₄ t₁ (CPSCons c₃ (CPSVar z₁) (CPSVar z₂))))
                 (λ z₃ →
                    cpsTerm (pcontext-plug p₂' (Val (Var z)))
                    (λ v t'' →
                       CPSApp
                       (CPSVal
                        (CPSFun
                         (λ t''' →
                            cpsTerm e₂
                            (λ v₂ t₄ →
                               CPSApp
                               (CPSApp (CPSApp (CPSVal v) (CPSVal v₂))
                                (CPSVal
                                 (CPSFun
                                  (λ v₃ →
                                     CPSVal (CPSFun (λ t'''' → k₁ (CPSVar v₃) (CPSVar t'''')))))))
                               (CPSVal t₄))
                            (CPSVar t'''))))
                       (CPSVal t''))
                    (CPSVar z₃)))))))))
    (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId)
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₁ → rFun (λ x₂ → rLet₂ (λ x₃ →
      correctCont (pcontext-plug p₂' (Val (Var x)))
        (λ v t'' →
           CPSApp
           (CPSVal
            (CPSFun
             (λ t''' →
                cpsTerm e₂
                (λ v₂ t₄ →
                   CPSApp
                   (CPSApp (CPSApp (CPSVal v) (CPSVal v₂))
                    (CPSVal
                     (CPSFun
                      (λ v₃ →
                         CPSVal (CPSFun (λ t'''' → k₁ (CPSVar v₃) (CPSVar t'''')))))))
                   (CPSVal t₄))
                (CPSVar t'''))))
           (CPSVal t''))
        {k₂ =
         λ v t'' →
           cpsTerm e₂
           (λ v₂ t₄ →
              CPSApp
              (CPSApp (CPSApp (CPSVal v) (CPSVal v₂))
               (CPSVal
                (CPSFun
                 (λ v₃ →
                    CPSVal (CPSFun (λ t'''' → k₁ (CPSVar v₃) (CPSVar t'''')))))))
              (CPSVal t₄))
           t''}
        (λ v t → sApp (sVal (sFun (λ x₄ →
        kSubst e₂
          (λ y →
             λ v₂ t₄ →
               CPSApp
               (CPSApp (CPSApp (CPSVal y) (CPSVal v₂))
                (CPSVal
                 (CPSFun
                  (λ v₃ →
                     CPSVal (CPSFun (λ t'''' → k₁ (CPSVar v₃) (CPSVar t'''')))))))
               (CPSVal t₄))
          (λ x₅ t₄ → sApp (sApp (sApp (sVal sVar=) Subst≠) Subst≠) Subst≠)))) Subst≠)
          (λ v t → rBeta (tSubst e₂ (λ t₄ v₂ → sApp Subst≠ (sVal sVar=))))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend c₄ t₁ (CPSCons c₃ (CPSVar z₁) (CPSVar z₂))))
                 (λ z₃ →
                    cpsTerm (pcontext-plug p₂' (Val (Var z)))
                    (λ v t'' →
                       cpsTerm e₂
                       (λ v₂ t₄ →
                          CPSApp
                          (CPSApp (CPSApp (CPSVal v) (CPSVal v₂))
                           (CPSVal
                            (CPSFun
                             (λ v₃ →
                                CPSVal (CPSFun (λ t'''' → k₁ (CPSVar v₃) (CPSVar t'''')))))))
                          (CPSVal t₄))
                       t'')
                    (CPSVar z₃)))))))))
    (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₁ → rFun (λ x₂ → rLet₂ (λ x₃ →
      correctCont (pcontext-plug p₂' (Val (Var x)))
        (λ v t'' →
           CPSApp
           (CPSVal
            (CPSFun
             (λ t''' →
                cpsTerm e₂
                (λ v₃ t₄ →
                   CPSApp
                   (CPSApp (CPSApp (CPSVal v) (CPSVal v₃))
                    (CPSVal
                     (CPSFun
                      (λ v₄ →
                         CPSVal (CPSFun (λ t'''' → k₁ (CPSVar v₄) (CPSVar t'''')))))))
                   (CPSVal t₄))
                (CPSVar t'''))))
           (CPSVal t''))
        {k₂ =
         λ v t'' →
           cpsTerm e₂
           (λ v₃ t₄ →
              CPSApp
              (CPSApp (CPSApp (CPSVal v) (CPSVal v₃))
               (CPSVal
                (CPSFun
                 (λ v₄ →
                    CPSVal (CPSFun (λ t'''' → k₁ (CPSVar v₄) (CPSVar t'''')))))))
              (CPSVal t₄))
           t''}
        (λ v t → sApp (sVal (sFun (λ x₄ →
        kSubst e₂
          (λ y →
             λ v₃ t₄ →
               CPSApp
               (CPSApp (CPSApp (CPSVal y) (CPSVal v₃))
                (CPSVal
                 (CPSFun
                  (λ v₄ →
                     CPSVal (CPSFun (λ t'''' → k₁ (CPSVar v₄) (CPSVar t'''')))))))
               (CPSVal t₄))
          (λ x₅ t₄ → sApp (sApp (sApp (sVal sVar=) Subst≠) Subst≠) Subst≠)))) Subst≠)
          (λ v t → rBeta (tSubst e₂ (λ t₄ v₂ → sApp Subst≠ (sVal sVar=))))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend c₄ t₁ (CPSCons c₃ (CPSVar z₁) (CPSVar z₂))))
                 (λ z₃ →
                    cpsTerm (pcontext-plug p₂' (Val (Var z)))
                    (λ v t'' →
                       CPSApp
                       (CPSVal
                        (CPSFun
                         (λ t''' →
                            cpsTerm e₂
                            (λ v₃ t₄ →
                               CPSApp
                               (CPSApp (CPSApp (CPSVal v) (CPSVal v₃))
                                (CPSVal
                                 (CPSFun
                                  (λ v₄ →
                                     CPSVal (CPSFun (λ t'''' → k₁ (CPSVar v₄) (CPSVar t'''')))))))
                               (CPSVal t₄))
                            (CPSVar t'''))))
                       (CPSVal t''))
                    (CPSVar z₃)))))))))
    (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₁ → rFun (λ x₂ → rLet₂ (λ x₃ →
      correctCont (pcontext-plug p₂' (Val (Var x)))
        (λ v₂ →
           cpsTerm e₂
           (λ v₃ t₄ →
              CPSApp
              (CPSApp (CPSApp (CPSVal v₂) (CPSVal v₃))
               (CPSVal
                (CPSFun
                 (λ v₄ →
                    CPSVal
                    (CPSFun
                     (λ t'''' →
                        CPSApp (CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t'''))))
                        (CPSVal (CPSVar t''''))))))))
              (CPSVal t₄)))
        {k₂ =
         λ v t'' →
           CPSApp
           (CPSVal
            (CPSFun
             (λ t''' →
                cpsTerm e₂
                (λ v₃ t₄ →
                   CPSApp
                   (CPSApp (CPSApp (CPSVal v) (CPSVal v₃))
                    (CPSVal
                     (CPSFun
                      (λ v₄ →
                         CPSVal (CPSFun (λ t'''' → k₁ (CPSVar v₄) (CPSVar t'''')))))))
                   (CPSVal t₄))
                (CPSVar t'''))))
           (CPSVal t'')}
        (λ v t → kSubst e₂
                     (λ x₄ →
                        λ v₃ t₄ →
                          CPSApp
                          (CPSApp (CPSApp (CPSVal x₄) (CPSVal v₃))
                           (CPSVal
                            (CPSFun
                             (λ v₄ →
                                CPSVal
                                (CPSFun
                                 (λ t'''' →
                                    CPSApp (CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t'''))))
                                    (CPSVal (CPSVar t''''))))))))
                          (CPSVal t₄))
                     (λ x₄ t₄ → sApp (sApp (sApp (sVal sVar=) Subst≠) Subst≠) Subst≠))
                     (λ v t → (begin
                     (cpsTerm e₂
       (λ v₃ t₄ →
          CPSApp
          (CPSApp (CPSApp (CPSVal (cpsV v)) (CPSVal v₃))
           (CPSVal
            (CPSFun
             (λ v₄ →
                CPSVal
                (CPSFun
                 (λ t'''' →
                    CPSApp (CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t'''))))
                    (CPSVal (CPSVar t''''))))))))
          (CPSVal t₄))
       t)
       ⟶⟨ correctCont e₂
            (λ v₃ t₄ →
               CPSApp
               (CPSApp (CPSApp (CPSVal (cpsV v)) (CPSVal v₃))
                (CPSVal
                 (CPSFun
                  (λ v₄ →
                     CPSVal
                     (CPSFun
                      (λ t'''' →
                         CPSApp (CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t'''))))
                         (CPSVal (CPSVar t''''))))))))
               (CPSVal t₄))
            {k₂ =
             λ z z₁ →
               CPSApp
               (CPSApp (CPSApp (CPSVal (cpsV v)) (CPSVal z))
                (CPSVal
                 (CPSFun
                  (λ v₄ →
                     CPSVal (CPSFun (λ t'''' → k₁ (CPSVar v₄) (CPSVar t'''')))))))
               (CPSVal z₁)}
            (λ v₁ t₄ → sApp (sApp (sApp Subst≠ (sVal sVar=)) Subst≠) Subst≠)
            (λ v₁ t₄ → rApp₁ (rApp₂ (rFun (λ x₄ → rFun (λ x₅ → rBeta (sch' (CPSVar x₅) (CPSVar x₄))))))) ⟩
       cpsTerm e₂
         (λ z z₁ →
            CPSApp
            (CPSApp (CPSApp (CPSVal (cpsV v)) (CPSVal z))
             (CPSVal
              (CPSFun
               (λ v₄ →
                  CPSVal (CPSFun (λ t'''' → k₁ (CPSVar v₄) (CPSVar t'''')))))))
            (CPSVal z₁))
         t
       ⟵⟨ rBeta (tSubst e₂ (λ t₄ v₂ → sApp Subst≠ (sVal sVar=))) ⟩
       (CPSApp
       (CPSVal
        (CPSFun
         (λ t''' →
            cpsTerm e₂
            (λ v₃ t₄ →
               CPSApp
               (CPSApp (CPSApp (CPSVal (cpsV v)) (CPSVal v₃))
                (CPSVal
                 (CPSFun
                  (λ v₄ →
                     CPSVal (CPSFun (λ t'''' → k₁ (CPSVar v₄) (CPSVar t'''')))))))
               (CPSVal t₄))
            (CPSVar t'''))))
       (CPSVal t))
       ∎))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend c₄ t₁ (CPSCons c₃ (CPSVar z₁) (CPSVar z₂))))
                 (λ z₃ →
                    cpsTerm (pcontext-plug p₂' (Val (Var z)))
                    (λ v₂ →
                       cpsTerm e₂
                       (λ v₃ t₄ →
                          CPSApp
                          (CPSApp (CPSApp (CPSVal v₂) (CPSVal v₃))
                           (CPSVal
                            (CPSFun
                             (λ v₄ →
                                CPSVal
                                (CPSFun
                                 (λ t'''' →
                                    CPSApp (CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t'''))))
                                    (CPSVal (CPSVar t''''))))))))
                          (CPSVal t₄)))
                    (CPSVar z₃)))))))))
    (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₁ → rFun (λ x₂ → rLet₂ (λ x₃ →
      correctCont (pcontext-plug p₂' (Val (Var x)))
        (λ v₁ →
           cpsTerm e₂
           (λ v₂ t₄ →
              CPSApp
              (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
               (CPSVal
                (CPSFun
                 (λ v₃ →
                    CPSVal
                    (CPSFun
                     (λ t'''' →
                        CPSApp
                        (CPSApp
                         (CPSVal
                          (CPSFun
                           (λ v₄ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t'''))))))
                         (CPSVal (CPSVar v₃)))
                        (CPSVal (CPSVar t''''))))))))
              (CPSVal t₄)))
        {k₂ =
         λ v₂ →
           cpsTerm e₂
           (λ v₃ t₄ →
              CPSApp
              (CPSApp (CPSApp (CPSVal v₂) (CPSVal v₃))
               (CPSVal
                (CPSFun
                 (λ v₄ →
                    CPSVal
                    (CPSFun
                     (λ t'''' →
                        CPSApp (CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t'''))))
                        (CPSVal (CPSVar t''''))))))))
              (CPSVal t₄))}
        (λ v t → kSubst e₂
                     (λ x₄ →
                        λ v₂ t₄ →
                          CPSApp
                          (CPSApp (CPSApp (CPSVal x₄) (CPSVal v₂))
                           (CPSVal
                            (CPSFun
                             (λ v₃ →
                                CPSVal
                                (CPSFun
                                 (λ t'''' →
                                    CPSApp
                                    (CPSApp
                                     (CPSVal
                                      (CPSFun
                                       (λ v₄ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t'''))))))
                                     (CPSVal (CPSVar v₃)))
                                    (CPSVal (CPSVar t''''))))))))
                          (CPSVal t₄))
                     (λ x₄ t₄ → sApp (sApp (sApp (sVal sVar=) Subst≠) Subst≠) Subst≠))
                     λ v t →
                     correctCont e₂
                       (λ v₂ t₄ →
                          CPSApp
                          (CPSApp (CPSApp (CPSVal (cpsV v)) (CPSVal v₂))
                           (CPSVal
                            (CPSFun
                             (λ v₃ →
                                CPSVal
                                (CPSFun
                                 (λ t'''' →
                                    CPSApp
                                    (CPSApp
                                     (CPSVal
                                      (CPSFun
                                       (λ v₄ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t'''))))))
                                     (CPSVal (CPSVar v₃)))
                                    (CPSVal (CPSVar t''''))))))))
                          (CPSVal t₄))
                       {k₂ =
                        λ v₃ t₄ →
                          CPSApp
                          (CPSApp (CPSApp (CPSVal (cpsV v)) (CPSVal v₃))
                           (CPSVal
                            (CPSFun
                             (λ v₄ →
                                CPSVal
                                (CPSFun
                                 (λ t'''' →
                                    CPSApp (CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t'''))))
                                    (CPSVal (CPSVar t''''))))))))
                          (CPSVal t₄)}
                       (λ v₁ t₄ → sApp (sApp (sApp Subst≠ (sVal sVar=)) Subst≠) Subst≠)
                       (λ v₁ t₄ → rApp₁ (rApp₂ (rFun (λ x₄ → rFun (λ x₅ → rApp₁ (rBeta
                       (sVal (sFun (λ x₆ → sch (CPSVar x₄) (CPSVar x₆))))))))))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend c₄ t₁ (CPSCons c₃ (CPSVar z₁) (CPSVar z₂))))
                 (λ z₃ →
                    cpsTerm (pcontext-plug p₂' (Val (Var z)))
                    (λ v₁ →
                       cpsTerm e₂
                       (λ v₂ t₄ →
                          CPSApp
                          (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
                           (CPSVal
                            (CPSFun
                             (λ v₃ →
                                CPSVal
                                (CPSFun
                                 (λ t'''' →
                                    CPSApp
                                    (CPSApp
                                     (CPSVal
                                      (CPSFun
                                       (λ v₄ →
                                          CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t'''))))))
                                     (CPSVal (CPSVar v₃)))
                                    (CPSVal (CPSVar t''''))))))))
                          (CPSVal t₄)))
                    (CPSVar z₃)))))))))
    (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₁ → rFun (λ x₂ → rLet₂ (λ x₃ → rBeta
      (tSubst (pcontext-plug p₂' (Val (Var x)))
      (λ t v₂ → tSubst e₂ (λ t₄ v₃ → sApp Subst≠ (sVal sVar=))))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend c₄ t₁ (CPSCons c₃ (CPSVar z₁) (CPSVar z₂))))
                 (λ z₃ →
                    CPSApp
                    (CPSVal
                     (CPSFun
                      (λ z₄ →
                         cpsTerm (pcontext-plug p₂' (Val (Var z)))
                         (λ v₁ →
                            cpsTerm e₂
                            (λ v₂ t₄ →
                               CPSApp
                               (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
                                (CPSVal
                                 (CPSFun
                                  (λ v₃ →
                                     CPSVal
                                     (CPSFun
                                      (λ t'''' →
                                         CPSApp
                                         (CPSApp
                                          (CPSVal
                                           (CPSFun
                                            (λ v₄ →
                                               CPSVal
                                               (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t'''))))))
                                          (CPSVal (CPSVar v₃)))
                                         (CPSVal (CPSVar t''''))))))))
                               (CPSVal t₄)))
                         (CPSVar z₄))))
                    (CPSVal (CPSVar z₃))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₁ → rFun (λ x₂ → rLet₂ (λ x₃ → rApp₁ (rBeta
      (sVal (sFun (λ x₄ →
      kSubst (pcontext-plug p₂' (Val (Var x)))
        (λ y →
           λ v₁ →
             cpsTerm e₂
             (λ v₂ t₄ →
                CPSApp
                (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
                 (CPSVal
                  (CPSFun
                   (λ v₃ →
                      CPSVal
                      (CPSFun
                       (λ t'''' →
                          CPSApp (CPSApp (CPSVal y) (CPSVal (CPSVar v₃)))
                          (CPSVal (CPSVar t''''))))))))
                (CPSVal t₄)))
        (λ x₅ t → kSubst e₂
                      (λ x₆ →
                         λ v₂ t₄ →
                           CPSApp
                           (CPSApp (CPSApp (CPSVal x₅) (CPSVal v₂))
                            (CPSVal
                             (CPSFun
                              (λ v₃ →
                                 CPSVal
                                 (CPSFun
                                  (λ t'''' →
                                     CPSApp (CPSApp (CPSVal x₆) (CPSVal (CPSVar v₃)))
                                     (CPSVal (CPSVar t''''))))))))
                           (CPSVal t₄))
                      (λ x₆ t₄ → sApp (sApp Subst≠
                      (sVal (sFun (λ x₇ → sVal (sFun (λ x₈ → sApp (sApp (sVal sVar=) Subst≠) Subst≠))))))
                      Subst≠))))))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend c₄ t₁ (CPSCons c₃ (CPSVar z₁) (CPSVar z₂))))
                 (λ z₃ →
                    CPSApp
                    (CPSApp
                     (CPSVal
                      (CPSFun
                       (λ z₄ →
                          CPSVal
                          (CPSFun
                           (λ z₅ →
                              cpsTerm (pcontext-plug p₂' (Val (Var z)))
                              (λ v₁ →
                                 cpsTerm e₂
                                 (λ v₂ t₄ →
                                    CPSApp
                                    (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
                                     (CPSVal
                                      (CPSFun
                                       (λ v₃ →
                                          CPSVal
                                          (CPSFun
                                           (λ t'''' →
                                              CPSApp (CPSApp (CPSVal (CPSVar z₄)) (CPSVal (CPSVar v₃)))
                                              (CPSVal (CPSVar t''''))))))))
                                    (CPSVal t₄)))
                              (CPSVar z₅))))))
                     (CPSVal
                      (CPSFun
                       (λ v₁ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₁) (CPSVar t''')))))))
                    (CPSVal (CPSVar z₃))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₁ → rFun (λ x₂ → rLet₂ (λ x₃ → rApp₁ (rApp₁ (rBeta
      (sVal (sFun (λ x₄ → sVal (sFun (λ x₅ →
      eSubst (subst-context p₂' (Var x))
      (λ {v₁} x₆ → kSubst′′ e₂
                       (λ x₇ →
                          λ v₂ t₄ →
                            CPSApp
                            (CPSApp (CPSApp (CPSVal (v₁ x₇)) (CPSVal v₂))
                             (CPSVal
                              (CPSFun
                               (λ v₃ →
                                  CPSVal
                                  (CPSFun
                                   (λ t'''' →
                                      CPSApp (CPSApp (CPSVal (CPSVar x₄)) (CPSVal (CPSVar v₃)))
                                      (CPSVal (CPSVar t''''))))))))
                            (CPSVal t₄))
                       (λ x₇ → sApp (sApp (sApp (sVal x₆) (sVal x₇)) Subst≠) Subst≠)))))))))))))) ⟩
  (CPSLet
       (CPSVal
        (CPSFun
         (λ v →
            CPSVal
            (CPSFun
             (λ k' →
                CPSVal
                (CPSFun
                 (λ t' →
                    CPSLet
                    (CPSVal (CPSAppend c₄ t₁ (CPSCons c₃ (CPSVar k') (CPSVar t'))))
                    (λ t'' →
                       CPSApp
                       (CPSApp
                        (CPSApp
                         (CPSVal
                          (CPSFun
                           (λ x →
                              CPSVal
                              (CPSFun
                               (λ k'' →
                                  CPSVal
                                  (CPSFun
                                   (λ t''' →
                                      cpsTerm (pcontext-plug p₂' (Val (Var x)))
                                      (λ v₁ →
                                         cpsTerm e₂
                                         (λ v₂ t₄ →
                                            CPSApp
                                            (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
                                             (CPSVal
                                              (CPSFun
                                               (λ v₃ →
                                                  CPSVal
                                                  (CPSFun
                                                   (λ t'''' →
                                                      CPSApp
                                                      (CPSApp (CPSVal (CPSVar k''))
                                                       (CPSVal (CPSVar v₃)))
                                                      (CPSVal (CPSVar t''''))))))))
                                            (CPSVal t₄)))
                                      (CPSVar t'''))))))))
                         (CPSVal (CPSVar v)))
                        (CPSVal
                         (CPSFun
                          (λ v₁ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₁) (CPSVar t''')))))))
                       (CPSVal (CPSVar t''))))))))))
       (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId))

  ∎


control-lemma
              (Frame (App₂ v₁) p₁') (Frame (App₂ .v₁) p₂') id₁ c₃ c₄
              (Frame {f₁ = (App₂ v₁)}{f₂ = (App₂ .v₁)} (App₂ .v₁) {c₁ = c₁}{c₂ = c₂} same) e k₁ t₁ sch sch' = begin

  (cpsTerm (pcontext-plug p₁' (Control id₁ c₃ c₄ e))
       (λ v₂ t₄ →
          CPSApp
          (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
           (CPSVal
            (CPSFun
             (λ v → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v) (CPSVar t'')))))))
          (CPSVal t₄))
       t₁)

  ⟶⟨ control-lemma p₁' p₂' id₁ c₃ c₄ same e
       (λ v₂ t₄ →
          CPSApp
          (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
           (CPSVal
            (CPSFun
             (λ v → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v) (CPSVar t'')))))))
          (CPSVal t₄))
       t₁ (λ v t → sApp (sApp (sApp Subst≠ (sVal sVar=)) Subst≠) Subst≠)
       (λ t v₂ → sApp Subst≠ (sVal sVar=)) ⟩
  cpsTerm {μs = {!!}}
    (App {μ[γ]β = {!!}} (Val (Fun (λ x → pcontext-plug p₂' (Val (Var x)))))
     (Control {μs₁ = {!!}} id₁ c₃ c₄ e))
    (λ v₂ t₄ →
       CPSApp
       (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
        (CPSVal
         (CPSFun
          (λ v → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v) (CPSVar t'')))))))
       (CPSVal t₄))
    t₁
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₁ → rFun (λ x₂ → rLet₂ (λ x₃ → rApp₁ (rApp₁ (rBeta
      (sVal (sFun (λ x₄ → sVal (sFun (λ x₅ → eSubst (subst-context p₂' (Var x))
      (λ x₆ → sApp (sApp Subst≠ (sVal x₆)) Subst≠))))))))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend c₄ t₁ (CPSCons c₃ (CPSVar z₁) (CPSVar z₂))))
                 (λ z₃ →
                    CPSApp
                    (CPSApp
                     (CPSVal
                      (CPSFun
                       (λ z₄ →
                          CPSVal
                          (CPSFun
                           (λ z₅ →
                              cpsTerm (pcontext-plug p₂' (Val (Var z)))
                              (λ v t'' →
                                 CPSApp (CPSApp (CPSVal (CPSVar z₄)) (CPSVal v)) (CPSVal t''))
                              (CPSVar z₅))))))
                     (CPSVal
                      (CPSFun
                       (λ v →
                          CPSVal
                          (CPSFun
                           (λ t'' →
                              CPSApp
                              (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal (CPSVar v)))
                               (CPSVal
                                (CPSFun
                                 (λ v₂ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₂) (CPSVar t''')))))))
                              (CPSVal (CPSVar t''))))))))
                    (CPSVal (CPSVar z₃))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId)
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₁ → rFun (λ x₂ → rLet₂ (λ x₃ → rApp₁ (rBeta
      (sVal (sFun (λ x₄ →
      kSubst (pcontext-plug p₂' (Val (Var x)))
        (λ y →
           λ v t'' → CPSApp (CPSApp (CPSVal y) (CPSVal v)) (CPSVal t''))
        (λ x₅ t → sApp (sApp (sVal sVar=) Subst≠) Subst≠)))))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend c₄ t₁ (CPSCons c₃ (CPSVar z₁) (CPSVar z₂))))
                 (λ z₃ →
                    CPSApp
                    (CPSVal
                     (CPSFun
                      (λ z₄ →
                         cpsTerm (pcontext-plug p₂' (Val (Var z)))
                         (λ v t'' →
                            CPSApp
                            (CPSApp
                             (CPSVal
                              (CPSFun
                               (λ v₂ →
                                  CPSVal
                                  (CPSFun
                                   (λ t''' →
                                      CPSApp
                                      (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal (CPSVar v₂)))
                                       (CPSVal
                                        (CPSFun
                                         (λ v₃ →
                                            CPSVal
                                            (CPSFun (λ t'''' → k₁ (CPSVar v₃) (CPSVar t'''')))))))
                                      (CPSVal (CPSVar t''')))))))
                             (CPSVal v))
                            (CPSVal t''))
                         (CPSVar z₄))))
                    (CPSVal (CPSVar z₃))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId)
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₁ → rFun (λ x₂ → rLet₂ (λ x₃ → rBeta
      (tSubst (pcontext-plug p₂' (Val (Var x)))
      (λ t v₂ → sApp Subst≠ (sVal sVar=)))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend c₄ t₁ (CPSCons c₃ (CPSVar z₁) (CPSVar z₂))))
                 (λ z₃ →
                    cpsTerm (pcontext-plug p₂' (Val (Var z)))
                    (λ v t'' →
                       CPSApp
                       (CPSApp
                        (CPSVal
                         (CPSFun
                          (λ v₂ →
                             CPSVal
                             (CPSFun
                              (λ t''' →
                                 CPSApp
                                 (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal (CPSVar v₂)))
                                  (CPSVal
                                   (CPSFun
                                    (λ v₃ →
                                       CPSVal (CPSFun (λ t'''' → k₁ (CPSVar v₃) (CPSVar t'''')))))))
                                 (CPSVal (CPSVar t''')))))))
                        (CPSVal v))
                       (CPSVal t''))
                    (CPSVar z₃)))))))))
    (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId)
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₁ → rFun (λ x₂ → rLet₂ (λ x₃ →
      correctCont (pcontext-plug p₂' (Val (Var x)))
        (λ v t'' →
           CPSApp
           (CPSApp
            (CPSVal
             (CPSFun
              (λ v₂ →
                 CPSVal
                 (CPSFun
                  (λ t''' →
                     CPSApp
                     (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal (CPSVar v₂)))
                      (CPSVal
                       (CPSFun
                        (λ v₃ →
                           CPSVal (CPSFun (λ t'''' → k₁ (CPSVar v₃) (CPSVar t'''')))))))
                     (CPSVal (CPSVar t''')))))))
            (CPSVal v))
           (CPSVal t''))
        {k₂ =
         λ v₂ t'''' →
           CPSApp
           (CPSVal
            (CPSFun
             (λ t''' →
                CPSApp
                (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
                 (CPSVal
                  (CPSFun
                   (λ v₄ →
                      CPSVal (CPSFun (λ t''''' → k₁ (CPSVar v₄) (CPSVar t''''')))))))
                (CPSVal (CPSVar t''')))))
           (CPSVal t'''')}
        (λ v t → sApp (sApp Subst≠ (sVal sVar=)) Subst≠)
        (λ v t → rApp₁ (rBeta (sVal (sFun (λ x₄ → sApp (sApp (sApp Subst≠ (sVal sVar=)) Subst≠) Subst≠)))))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend c₄ t₁ (CPSCons c₃ (CPSVar z₁) (CPSVar z₂))))
                 (λ z₃ →
                    cpsTerm (pcontext-plug p₂' (Val (Var z)))
                    (λ v₂ t'''' →
                       CPSApp
                       (CPSVal
                        (CPSFun
                         (λ t''' →
                            CPSApp
                            (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
                             (CPSVal
                              (CPSFun
                               (λ v₄ →
                                  CPSVal (CPSFun (λ t''''' → k₁ (CPSVar v₄) (CPSVar t''''')))))))
                            (CPSVal (CPSVar t''')))))
                       (CPSVal t''''))
                    (CPSVar z₃)))))))))
    (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId)
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₁ → rFun (λ x₂ → rLet₂ (λ x₃ →
      correctCont (pcontext-plug p₂' (Val (Var x)))
        (λ v₂ t'''' →
           CPSApp
           (CPSVal
            (CPSFun
             (λ t''' →
                CPSApp
                (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
                 (CPSVal
                  (CPSFun
                   (λ v₄ →
                      CPSVal (CPSFun (λ t''''' → k₁ (CPSVar v₄) (CPSVar t''''')))))))
                (CPSVal (CPSVar t''')))))
           (CPSVal t''''))
        {k₂ =
         λ v₂ t'''' →
           CPSApp
           (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
            (CPSVal
             (CPSFun
              (λ v₄ →
                 CPSVal (CPSFun (λ t''''' → k₁ (CPSVar v₄) (CPSVar t''''')))))))
           (CPSVal t'''')}
        (λ v t → sApp (sVal (sFun (λ x₄ → sApp (sApp (sApp Subst≠ (sVal sVar=)) Subst≠) Subst≠))) Subst≠)
        (λ v t → rBeta (sApp Subst≠ (sVal sVar=)))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend c₄ t₁ (CPSCons c₃ (CPSVar z₁) (CPSVar z₂))))
                 (λ z₃ →
                    cpsTerm (pcontext-plug p₂' (Val (Var z)))
                    (λ v₂ t'''' →
                       CPSApp
                       (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
                        (CPSVal
                         (CPSFun
                          (λ v₄ →
                             CPSVal (CPSFun (λ t''''' → k₁ (CPSVar v₄) (CPSVar t''''')))))))
                       (CPSVal t''''))
                    (CPSVar z₃)))))))))
    (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₁ → rFun (λ x₂ → rLet₂ (λ x₃ →
      correctCont (pcontext-plug p₂' (Val (Var x)))
        (λ v₂ t₄ →
           CPSApp
           (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
            (CPSVal
             (CPSFun
              (λ v₃ →
                 CPSVal
                 (CPSFun
                  (λ t'''' →
                     CPSApp (CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₃) (CPSVar t'''))))
                     (CPSVal (CPSVar t''''))))))))
           (CPSVal t₄))
        {k₂ =
         λ v₂ t₄ →
           CPSApp
           (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
            (CPSVal
             (CPSFun
              (λ v₃ →
                 CPSVal (CPSFun (λ t'''' → k₁ (CPSVar v₃) (CPSVar t'''')))))))
           (CPSVal t₄)}
        (λ v t → sApp (sApp (sApp Subst≠ (sVal sVar=)) Subst≠) Subst≠)
        (λ v t → rApp₁ (rApp₂ (rFun (λ x₄ → rFun (λ x₅ → rBeta (sch' (CPSVar x₅) (CPSVar x₄)))))))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend c₄ t₁ (CPSCons c₃ (CPSVar z₁) (CPSVar z₂))))
                 (λ z₃ →
                    cpsTerm (pcontext-plug p₂' (Val (Var z)))
                    (λ v₂ t₄ →
                       CPSApp
                       (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
                        (CPSVal
                         (CPSFun
                          (λ v₃ →
                             CPSVal
                             (CPSFun
                              (λ t'''' →
                                 CPSApp (CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₃) (CPSVar t'''))))
                                 (CPSVal (CPSVar t''''))))))))
                       (CPSVal t₄))
                    (CPSVar z₃)))))))))
    (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₁ → rFun (λ x₂ → rLet₂ (λ x₃ →
      correctCont (pcontext-plug p₂' (Val (Var x)))
        (λ v₂ t₄ →
           CPSApp
           (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
            (CPSVal
             (CPSFun
              (λ v₃ →
                 CPSVal
                 (CPSFun
                  (λ t'''' →
                     CPSApp
                     (CPSApp
                      (CPSVal
                       (CPSFun
                        (λ v₄ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t'''))))))
                      (CPSVal (CPSVar v₃)))
                     (CPSVal (CPSVar t''''))))))))
           (CPSVal t₄))
        {k₂ =
         λ v₂ t₄ →
           CPSApp
           (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
            (CPSVal
             (CPSFun
              (λ v₃ →
                 CPSVal
                 (CPSFun
                  (λ t'''' →
                     CPSApp (CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₃) (CPSVar t'''))))
                     (CPSVal (CPSVar t''''))))))))
           (CPSVal t₄)}
        (λ v t → sApp (sApp (sApp Subst≠ (sVal sVar=)) Subst≠) Subst≠)
        (λ v t → rApp₁ (rApp₂ (rFun (λ x₄ → rFun (λ x₅ → rApp₁ (rBeta
        (sVal (sFun (λ x₆ → sch (CPSVar x₄) (CPSVar x₆))))))))))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend c₄ t₁ (CPSCons c₃ (CPSVar z₁) (CPSVar z₂))))
                 (λ z₃ →
                    cpsTerm (pcontext-plug p₂' (Val (Var z)))
                    (λ v₂ t₄ →
                       CPSApp
                       (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
                        (CPSVal
                         (CPSFun
                          (λ v₃ →
                             CPSVal
                             (CPSFun
                              (λ t'''' →
                                 CPSApp
                                 (CPSApp
                                  (CPSVal
                                   (CPSFun
                                    (λ v₄ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t'''))))))
                                  (CPSVal (CPSVar v₃)))
                                 (CPSVal (CPSVar t''''))))))))
                       (CPSVal t₄))
                    (CPSVar z₃)))))))))
    (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₁ → rFun (λ x₂ → rLet₂ (λ x₃ → rBeta
      (tSubst (pcontext-plug p₂' (Val (Var x))) (λ t v₂ → sApp Subst≠ (sVal sVar=)))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend c₄ t₁ (CPSCons c₃ (CPSVar z₁) (CPSVar z₂))))
                 (λ z₃ →
                    CPSApp
                    (CPSVal
                     (CPSFun
                      (λ z₄ →
                         cpsTerm (pcontext-plug p₂' (Val (Var z)))
                         (λ v₂ t₄ →
                            CPSApp
                            (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
                             (CPSVal
                              (CPSFun
                               (λ v₃ →
                                  CPSVal
                                  (CPSFun
                                   (λ t'''' →
                                      CPSApp
                                      (CPSApp
                                       (CPSVal
                                        (CPSFun
                                         (λ v₄ →
                                            CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t'''))))))
                                       (CPSVal (CPSVar v₃)))
                                      (CPSVal (CPSVar t''''))))))))
                            (CPSVal t₄))
                         (CPSVar z₄))))
                    (CPSVal (CPSVar z₃))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₁ → rFun (λ x₂ → rLet₂ (λ x₃ → rApp₁ (rBeta
      (sVal (sFun (λ x₄ →
      kSubst (pcontext-plug p₂' (Val (Var x)))
        (λ y →
           λ v₂ t₄ →
             CPSApp
             (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
              (CPSVal
               (CPSFun
                (λ v₃ →
                   CPSVal
                   (CPSFun
                    (λ t'''' →
                       CPSApp (CPSApp (CPSVal y) (CPSVal (CPSVar v₃)))
                       (CPSVal (CPSVar t''''))))))))
             (CPSVal t₄))
        (λ x₅ t → sApp (sApp Subst≠ (sVal (sFun (λ x₆ → sVal (sFun (λ x₇ →
        sApp (sApp (sVal sVar=) Subst≠) Subst≠)))))) Subst≠)))))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend c₄ t₁ (CPSCons c₃ (CPSVar z₁) (CPSVar z₂))))
                 (λ z₃ →
                    CPSApp
                    (CPSApp
                     (CPSVal
                      (CPSFun
                       (λ z₄ →
                          CPSVal
                          (CPSFun
                           (λ z₅ →
                              cpsTerm (pcontext-plug p₂' (Val (Var z)))
                              (λ v₂ t₄ →
                                 CPSApp
                                 (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
                                  (CPSVal
                                   (CPSFun
                                    (λ v₃ →
                                       CPSVal
                                       (CPSFun
                                        (λ t'''' →
                                           CPSApp (CPSApp (CPSVal (CPSVar z₄)) (CPSVal (CPSVar v₃)))
                                           (CPSVal (CPSVar t''''))))))))
                                 (CPSVal t₄))
                              (CPSVar z₅))))))
                     (CPSVal
                      (CPSFun
                       (λ v₂ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₂) (CPSVar t''')))))))
                    (CPSVal (CPSVar z₃))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₁ → rFun (λ x₂ → rLet₂ (λ x₃ → rApp₁ (rApp₁ (rBeta
      (sVal (sFun (λ x₄ → sVal (sFun (λ x₅ →
      eSubst (subst-context p₂' (Var x))
      (λ x₆ → sApp (sApp (sApp Subst≠ (sVal x₆)) Subst≠) Subst≠))))))))))))) ⟩
  (CPSLet
       (CPSVal
        (CPSFun
         (λ v →
            CPSVal
            (CPSFun
             (λ k' →
                CPSVal
                (CPSFun
                 (λ t' →
                    CPSLet
                    (CPSVal (CPSAppend c₄ t₁ (CPSCons c₃ (CPSVar k') (CPSVar t'))))
                    (λ t'' →
                       CPSApp
                       (CPSApp
                        (CPSApp
                         (CPSVal
                          (CPSFun
                           (λ x →
                              CPSVal
                              (CPSFun
                               (λ k'' →
                                  CPSVal
                                  (CPSFun
                                   (λ t''' →
                                      cpsTerm (pcontext-plug p₂' (Val (Var x)))
                                      (λ v₂ t₄ →
                                         CPSApp
                                         (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
                                          (CPSVal
                                           (CPSFun
                                            (λ v₃ →
                                               CPSVal
                                               (CPSFun
                                                (λ t'''' →
                                                   CPSApp
                                                   (CPSApp (CPSVal (CPSVar k''))
                                                    (CPSVal (CPSVar v₃)))
                                                   (CPSVal (CPSVar t''''))))))))
                                         (CPSVal t₄))
                                      (CPSVar t'''))))))))
                         (CPSVal (CPSVar v)))
                        (CPSVal
                         (CPSFun
                          (λ v₂ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₂) (CPSVar t''')))))))
                       (CPSVal (CPSVar t''))))))))))
       (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId))

  ∎


control-lemma 
              (Frame (Plus₁ e₂) p₁') (Frame (Plus₁ .e₂) p₂') id₁ c₃ c₄
              (Frame {f₁ = (Plus₁ e₂)}{f₂ = (Plus₁ .e₂)} (Plus₁ .e₂) {c₁ = c₁}{c₂ = c₂} same) e k₁ tr sch sch' = begin

  (cpsTerm (pcontext-plug p₁' (Control id₁ c₃ c₄ e))
       (λ v₁ →
          cpsTerm e₂
          (λ v₂ t₃ →
             CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂)) (λ v → k₁ (CPSVar v) t₃)))
       tr)

  ⟶⟨ control-lemma p₁' p₂' id₁ c₃ c₄ same e
       (λ v₁ →
          cpsTerm e₂
          (λ v₂ t₃ →
             CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂)) (λ v → k₁ (CPSVar v) t₃)))
       tr
       (λ v t → kSubst e₂
                    (λ x →
                       λ v₂ t₃ →
                         CPSLet (CPSPlus (CPSVal x) (CPSVal v₂)) (λ v₁ → k₁ (CPSVar v₁) t₃))
                    (λ x t₃ → sLet (λ x₁ → Subst≠) (λ x₁ → sPlu (sVal sVar=) Subst≠)))
                    (λ t v₂ → tSubst e₂ (λ t₃ v₃ → sLet (λ x → sch' t₃ (CPSVar x)) (λ x → Subst≠))) ⟩
  cpsTerm {μs = {!!}}
    (App {μ[γ]β = {!!}} (Val (Fun (λ x → pcontext-plug p₂' (Val (Var x)))))
     (Control {μs₁ = {!!}} id₁ c₃ c₄ e))
    (λ v₁ →
       cpsTerm e₂
       (λ v₂ t₃ →
          CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂)) (λ v → k₁ (CPSVar v) t₃)))
    tr
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₁ → rFun (λ x₂ → rLet₂ (λ x₃ → rApp₁ (rApp₁ (rBeta
      (sVal (sFun (λ x₄ → sVal (sFun (λ x₅ →
      eSubst (subst-context p₂' (Var x)) (λ x₆ → sApp (sApp Subst≠ (sVal x₆)) Subst≠))))))))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend c₄ tr (CPSCons c₃ (CPSVar z₁) (CPSVar z₂))))
                 (λ z₃ →
                    CPSApp
                    (CPSApp
                     (CPSVal
                      (CPSFun
                       (λ z₄ →
                          CPSVal
                          (CPSFun
                           (λ z₅ →
                              cpsTerm (pcontext-plug p₂' (Val (Var z)))
                              (λ v t'' →
                                 CPSApp (CPSApp (CPSVal (CPSVar z₄)) (CPSVal v)) (CPSVal t''))
                              (CPSVar z₅))))))
                     (CPSVal
                      (CPSFun
                       (λ v →
                          CPSVal
                          (CPSFun
                           (λ t'' →
                              cpsTerm e₂
                              (λ v₂ t₃ →
                                 CPSLet (CPSPlus (CPSVal (CPSVar v)) (CPSVal v₂))
                                 (λ v₁ → k₁ (CPSVar v₁) t₃))
                              (CPSVar t'')))))))
                    (CPSVal (CPSVar z₃))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId)
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₁ → rFun (λ x₂ → rLet₂ (λ x₃ → rApp₁ (rBeta
      (sVal (sFun (λ x₄ →
      kSubst (pcontext-plug p₂' (Val (Var x)))
        (λ y →
           λ v t'' → CPSApp (CPSApp (CPSVal y) (CPSVal v)) (CPSVal t''))
        (λ x₅ t → sApp (sApp (sVal sVar=) Subst≠) Subst≠)))))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend c₄ tr (CPSCons c₃ (CPSVar z₁) (CPSVar z₂))))
                 (λ z₃ →
                    CPSApp
                    (CPSVal
                     (CPSFun
                      (λ z₄ →
                         cpsTerm (pcontext-plug p₂' (Val (Var z)))
                         (λ v t'' →
                            CPSApp
                            (CPSApp
                             (CPSVal
                              (CPSFun
                               (λ v₁ →
                                  CPSVal
                                  (CPSFun
                                   (λ t''' →
                                      cpsTerm e₂
                                      (λ v₂ t₃ →
                                         CPSLet (CPSPlus (CPSVal (CPSVar v₁)) (CPSVal v₂))
                                         (λ v₃ → k₁ (CPSVar v₃) t₃))
                                      (CPSVar t'''))))))
                             (CPSVal v))
                            (CPSVal t''))
                         (CPSVar z₄))))
                    (CPSVal (CPSVar z₃))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId)
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₁ → rFun (λ x₂ → rLet₂ (λ x₃ → rBeta
      (tSubst (pcontext-plug p₂' (Val (Var x)))
      (λ t v₂ → sApp Subst≠ (sVal sVar=)))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend c₄ tr (CPSCons c₃ (CPSVar z₁) (CPSVar z₂))))
                 (λ z₃ →
                    cpsTerm (pcontext-plug p₂' (Val (Var z)))
                    (λ v t'' →
                       CPSApp
                       (CPSApp
                        (CPSVal
                         (CPSFun
                          (λ v₁ →
                             CPSVal
                             (CPSFun
                              (λ t''' →
                                 cpsTerm e₂
                                 (λ v₂ t₃ →
                                    CPSLet (CPSPlus (CPSVal (CPSVar v₁)) (CPSVal v₂))
                                    (λ v₃ → k₁ (CPSVar v₃) t₃))
                                 (CPSVar t'''))))))
                        (CPSVal v))
                       (CPSVal t''))
                    (CPSVar z₃)))))))))
    (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId)
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₁ → rFun (λ x₂ → rLet₂ (λ x₃ →
      correctCont (pcontext-plug p₂' (Val (Var x)))
        (λ v t'' →
           CPSApp
           (CPSApp
            (CPSVal
             (CPSFun
              (λ v₁ →
                 CPSVal
                 (CPSFun
                  (λ t''' →
                     cpsTerm e₂
                     (λ v₂ t₃ →
                        CPSLet (CPSPlus (CPSVal (CPSVar v₁)) (CPSVal v₂))
                        (λ v₃ → k₁ (CPSVar v₃) t₃))
                     (CPSVar t'''))))))
            (CPSVal v))
           (CPSVal t''))
        {k₂ =
         λ v₁ t'''' →
           CPSApp
           (CPSVal
            (CPSFun
             (λ t''' →
                cpsTerm e₂
                (λ v₃ t₄ →
                   CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₃))
                   (λ v₄ → k₁ (CPSVar v₄) t₄))
                (CPSVar t'''))))
           (CPSVal t'''')}
        (λ v t → sApp (sApp Subst≠ (sVal sVar=)) Subst≠)
        (λ v t → rApp₁ (rBeta (sVal (sFun (λ x₄ →
        kSubst e₂
          (λ y →
             λ v₂ t₃ →
               CPSLet (CPSPlus (CPSVal y) (CPSVal v₂)) (λ v₃ → k₁ (CPSVar v₃) t₃))
          (λ x₅ t₃ → sLet (λ x₆ → Subst≠) (λ x₆ → sPlu (sVal sVar=) Subst≠)))))))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend c₄ tr (CPSCons c₃ (CPSVar z₁) (CPSVar z₂))))
                 (λ z₃ →
                    cpsTerm (pcontext-plug p₂' (Val (Var z)))
                    (λ v₁ t'''' →
                       CPSApp
                       (CPSVal
                        (CPSFun
                         (λ t''' →
                            cpsTerm e₂
                            (λ v₃ t₄ →
                               CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₃))
                               (λ v₄ → k₁ (CPSVar v₄) t₄))
                            (CPSVar t'''))))
                       (CPSVal t''''))
                    (CPSVar z₃)))))))))
    (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId)
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₁ → rFun (λ x₂ → rLet₂ (λ x₃ →
      correctCont (pcontext-plug p₂' (Val (Var x)))
        (λ v₁ t'''' →
           CPSApp
           (CPSVal
            (CPSFun
             (λ t''' →
                cpsTerm e₂
                (λ v₃ t₄ →
                   CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₃))
                   (λ v₄ → k₁ (CPSVar v₄) t₄))
                (CPSVar t'''))))
           (CPSVal t''''))
        {k₂ =
         λ v₁ t'''' →
           cpsTerm e₂
           (λ v₃ t₄ →
              CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₃))
              (λ v₄ → k₁ (CPSVar v₄) t₄))
           t''''}
        (λ v t → sApp (sVal (sFun (λ x₄ →
          kSubst e₂
            (λ y →
               λ v₃ t₄ →
                 CPSLet (CPSPlus (CPSVal y) (CPSVal v₃)) (λ v₄ → k₁ (CPSVar v₄) t₄))
            (λ x₅ t₃ → sLet (λ x₆ → Subst≠) (λ x₆ → sPlu (sVal sVar=) Subst≠))))) Subst≠)
            (λ v t → rBeta (tSubst e₂ (λ t₃ v₂ → sLet (λ x₄ → sch' t₃ (CPSVar x₄)) (λ x₄ → Subst≠))))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend c₄ tr (CPSCons c₃ (CPSVar z₁) (CPSVar z₂))))
                 (λ z₃ →
                    cpsTerm (pcontext-plug p₂' (Val (Var z)))
                    (λ v₁ t'''' →
                       cpsTerm e₂
                       (λ v₃ t₄ →
                          CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₃))
                          (λ v₄ → k₁ (CPSVar v₄) t₄))
                       t'''')
                    (CPSVar z₃)))))))))
    (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId)
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₁ → rFun (λ x₂ → rLet₂ (λ x₃ →
      correctCont (pcontext-plug p₂' (Val (Var x)))
        (λ v₁ t'''' →
           cpsTerm e₂
           (λ v₃ t₄ →
              CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₃))
              (λ v₄ → k₁ (CPSVar v₄) t₄))
           t'''')
        {k₂ =
         λ v₁ →
           cpsTerm e₂
           (λ v₂ t₄ →
              CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂))
              (λ v₃ → k₁ (CPSVar v₃) t₄))}
        (λ v t → kSubst e₂
                     (λ x₄ →
                        λ v₃ t₄ →
                          CPSLet (CPSPlus (CPSVal x₄) (CPSVal v₃))
                          (λ v₄ → k₁ (CPSVar v₄) t₄))
                     (λ x₄ t₃ → sLet (λ x₅ → Subst≠) (λ x₅ → sPlu (sVal sVar=) Subst≠)))
                     (λ v t → correctCont e₂
                                  (λ v₃ t₄ →
                                     CPSLet (CPSPlus (CPSVal (cpsV v)) (CPSVal v₃))
                                     (λ v₄ → k₁ (CPSVar v₄) t₄))
                                  {k₂ =
                                   λ v₂ t₄ →
                                     CPSLet (CPSPlus (CPSVal (cpsV v)) (CPSVal v₂))
                                     (λ v₃ → k₁ (CPSVar v₃) t₄)}
                                  (λ v₁ t₃ → sLet (λ x₄ → Subst≠) (λ x₄ → sPlu Subst≠ (sVal sVar=)))
                                  (λ v₁ t₃ → rLet₂ (λ x₄ → r*Id)))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend c₄ tr (CPSCons c₃ (CPSVar z₁) (CPSVar z₂))))
                 (λ z₃ →
                    cpsTerm (pcontext-plug p₂' (Val (Var z)))
                    (λ v₁ →
                       cpsTerm e₂
                       (λ v₂ t₄ →
                          CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂))
                          (λ v₃ → k₁ (CPSVar v₃) t₄)))
                    (CPSVar z₃)))))))))
    (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ →
      correctCont (pcontext-plug p₂' (Val (Var x)))
        (λ v₁ →
           cpsTerm e₂
           (λ v₂ t₄ →
              CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂))
              (λ v₃ →
                 CPSApp (CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₃) (CPSVar t'''))))
                 (CPSVal t₄))))
                 {k₂ = (λ v₁ →
          cpsTerm e₂
          (λ v₂ t₄ →
             CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂))
             (λ v₃ →
                k₁ (CPSVar v₃) t₄ )))}
        (λ v t → kSubst e₂
                     (λ x₈ →
                        λ v₂ t₄ →
                          CPSLet (CPSPlus (CPSVal x₈) (CPSVal v₂))
                          (λ v₃ →
                             CPSApp (CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₃) (CPSVar t'''))))
                             (CPSVal t₄)))
                     (λ x₈ t₄ → sLet (λ x₉ → sApp Subst≠ Subst≠) (λ x₉ → sPlu (sVal sVar=) Subst≠)))
                     λ v t → correctCont e₂
                                 (λ v₂ t₄ →
                                    CPSLet (CPSPlus (CPSVal (cpsV v)) (CPSVal v₂))
                                    (λ v₃ →
                                       CPSApp (CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₃) (CPSVar t'''))))
                                       (CPSVal t₄)))
                              {k₂ = (λ v₂ t₄ →
          CPSLet (CPSPlus (CPSVal (cpsV v)) (CPSVal v₂))
          (λ v₃ →
             k₁ (CPSVar v₃) t₄))}
                                 (λ v₁ t₄ → sLet (λ x₈ → sApp Subst≠ Subst≠)
                                 (λ x₈ → sPlu Subst≠ (sVal sVar=)))
                                 λ v₁ t₄ → rLet₂ (λ x₈ → rBeta (sch' t₄ (CPSVar x₈)))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend c₄ tr (CPSCons c₃ (CPSVar z₁) (CPSVar z₂))))
                 (λ z₃ →
                    cpsTerm (pcontext-plug p₂' (Val (Var z)))
                    (λ v₁ →
                       cpsTerm e₂
                       (λ v₂ t₄ →
                          CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂))
                          (λ v₃ →
                             CPSApp (CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₃) (CPSVar t'''))))
                             (CPSVal t₄))))
                    (CPSVar z₃)))))))))
    (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ →
      correctCont (pcontext-plug p₂' (Val (Var x)))
        (λ v₁ →
           cpsTerm e₂
           (λ v₂ t₄ →
              CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂))
              (λ v₃ →
                 CPSApp
                 (CPSApp
                  (CPSVal
                   (CPSFun
                    (λ v₄ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t'''))))))
                  (CPSVal (CPSVar v₃)))
                 (CPSVal t₄))))
                 {k₂ = (λ v₁ →
          cpsTerm e₂
          (λ v₂ t₄ →
             CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂))
             (λ v₃ →
                CPSApp
                (CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₃) (CPSVar t'''))))
                 
                (CPSVal t₄))))}
        (λ v t → kSubst e₂
                     (λ x₈ →
                        λ v₂ t₄ →
                          CPSLet (CPSPlus (CPSVal x₈) (CPSVal v₂))
                          (λ v₃ →
                             CPSApp
                             (CPSApp
                              (CPSVal
                               (CPSFun
                                (λ v₄ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t'''))))))
                              (CPSVal (CPSVar v₃)))
                             (CPSVal t₄)))
                     (λ x₈ t₄ → sLet (λ x₉ → sApp Subst≠ Subst≠) (λ x₉ → sPlu (sVal sVar=) Subst≠)))
                     λ v t → correctCont e₂
                                 (λ v₂ t₄ →
                                    CPSLet (CPSPlus (CPSVal (cpsV v)) (CPSVal v₂))
                                    (λ v₃ →
                                       CPSApp
                                       (CPSApp
                                        (CPSVal
                                         (CPSFun
                                          (λ v₄ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t'''))))))
                                        (CPSVal (CPSVar v₃)))
                                       (CPSVal t₄)))
                                       {k₂ = (λ v₂ t₄ →
          CPSLet (CPSPlus (CPSVal (cpsV v)) (CPSVal v₂))
          (λ v₃ →
             CPSApp (CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₃) (CPSVar t'''))))
             (CPSVal t₄)))}
                                 (λ v₁ t₄ → sLet (λ x₈ → sApp Subst≠ Subst≠)
                                 (λ x₈ → sPlu Subst≠ (sVal sVar=))) λ v₁ t₄ →
                                 rLet₂ (λ x₈ → rApp₁ (rBeta (sVal (sFun (λ x₉ → sch (CPSVar x₈) (CPSVar x₉))))))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend c₄ tr (CPSCons c₃ (CPSVar z₁) (CPSVar z₂))))
                 (λ z₃ →
                    cpsTerm (pcontext-plug p₂' (Val (Var z)))
                    (λ v₁ →
                       cpsTerm e₂
                       (λ v₂ t₄ →
                          CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂))
                          (λ v₃ →
                             CPSApp
                             (CPSApp
                              (CPSVal
                               (CPSFun
                                (λ v₄ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t'''))))))
                              (CPSVal (CPSVar v₃)))
                             (CPSVal t₄))))
                    (CPSVar z₃)))))))))
    (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ → rBeta
      (tSubst (pcontext-plug p₂' (Val (Var x))) (λ t v₂ →
      tSubst e₂ (λ t₄ v₃ → sLet (λ x₈ → sApp Subst≠ (sVal sVar=)) (λ x₈ → Subst≠))))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend c₄ tr (CPSCons c₃ (CPSVar z₁) (CPSVar z₂))))
                 (λ z₃ →
                    CPSApp
                    (CPSVal
                     (CPSFun
                      (λ z₄ →
                         cpsTerm (pcontext-plug p₂' (Val (Var z)))
                         (λ v₁ →
                            cpsTerm e₂
                            (λ v₂ t₄ →
                               CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂))
                               (λ v₃ →
                                  CPSApp
                                  (CPSApp
                                   (CPSVal
                                    (CPSFun
                                     (λ v₄ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t'''))))))
                                   (CPSVal (CPSVar v₃)))
                                  (CPSVal t₄))))
                         (CPSVar z₄))))
                    (CPSVal (CPSVar z₃))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ → rApp₁ (rBeta
      (sVal (sFun (λ x₈ →
      kSubst (pcontext-plug p₂' (Val (Var x)))
        (λ y →
           λ v₁ →
             cpsTerm e₂
             (λ v₂ t₄ →
                CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂))
                (λ v₃ →
                   CPSApp (CPSApp (CPSVal y) (CPSVal (CPSVar v₃))) (CPSVal t₄))))
        (λ x₉ t → kSubst e₂
                      (λ x₁₀ →
                         λ v₂ t₄ →
                           CPSLet (CPSPlus (CPSVal x₉) (CPSVal v₂))
                           (λ v₃ →
                              CPSApp (CPSApp (CPSVal x₁₀) (CPSVal (CPSVar v₃))) (CPSVal t₄)))
                      (λ x₁₀ t₄ → sLet (λ x₁₁ → sApp (sApp (sVal sVar=) Subst≠) Subst≠) (λ x₁₁ → Subst≠)))))))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend c₄ tr (CPSCons c₃ (CPSVar z₁) (CPSVar z₂))))
                 (λ z₃ →
                    CPSApp
                    (CPSApp
                     (CPSVal
                      (CPSFun
                       (λ z₄ →
                          CPSVal
                          (CPSFun
                           (λ z₅ →
                              cpsTerm (pcontext-plug p₂' (Val (Var z)))
                              (λ v₁ →
                                 cpsTerm e₂
                                 (λ v₂ t₃ →
                                    CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂))
                                    (λ v₃ →
                                       CPSApp (CPSApp (CPSVal (CPSVar z₄)) (CPSVal (CPSVar v₃)))
                                       (CPSVal t₃))))
                              (CPSVar z₅))))))
                     (CPSVal
                      (CPSFun
                       (λ v₁ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₁) (CPSVar t''')))))))
                    (CPSVal (CPSVar z₃))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ →
      rApp₁ (rApp₁ (rBeta (sVal (sFun (λ x₈ → sVal (sFun (λ x₉ → eSubst (subst-context p₂' (Var x))
      (λ {v₁} x₁₀ → kSubst′′ e₂
                        (λ x₁₁ →
                           λ v₂ t₄ →
                             CPSLet (CPSPlus (CPSVal (v₁ x₁₁)) (CPSVal v₂))
                             (λ v₃ →
                                CPSApp (CPSApp (CPSVal (CPSVar x₈)) (CPSVal (CPSVar v₃)))
                                (CPSVal t₄)))
                        (λ x₁₁ → sLet (λ x₁₂ → sApp Subst≠ Subst≠)
                        (λ x₁₂ → sPlu (sVal x₁₀) (sVal x₁₁)))))))))))))))) ⟩
  (CPSLet
       (CPSVal
        (CPSFun
         (λ v →
            CPSVal
            (CPSFun
             (λ k' →
                CPSVal
                (CPSFun
                 (λ t' →
                    CPSLet
                    (CPSVal (CPSAppend c₄ tr (CPSCons c₃ (CPSVar k') (CPSVar t'))))
                    (λ t'' →
                       CPSApp
                       (CPSApp
                        (CPSApp
                         (CPSVal
                          (CPSFun
                           (λ x →
                              CPSVal
                              (CPSFun
                               (λ k'' →
                                  CPSVal
                                  (CPSFun
                                   (λ t''' →
                                      cpsTerm (pcontext-plug p₂' (Val (Var x)))
                                      (λ v₁ →
                                         cpsTerm e₂
                                         (λ v₂ t₃ →
                                            CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂))
                                            (λ v₃ →
                                               CPSApp
                                               (CPSApp (CPSVal (CPSVar k'')) (CPSVal (CPSVar v₃)))
                                               (CPSVal t₃))))
                                      (CPSVar t'''))))))))
                         (CPSVal (CPSVar v)))
                        (CPSVal
                         (CPSFun
                          (λ v₁ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₁) (CPSVar t''')))))))
                       (CPSVal (CPSVar t''))))))))))
       (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId))

  ∎

-- control-lemma {μα = μα}{μ[μ₂]μ₁ = μ[μ₂]μ₁}{μ[β]α = μ[β]α}
--               (Frame (App₁ e₂) p₁') (Frame (App₁ .e₂) p₂') id₁ c₃ c₄
--               (Frame {f₁ = (App₁ e₂)}{f₂ = (App₁ .e₂)} (App₁ .e₂) {c₁ = c₁}{c₂ = c₂} same) e k₁ t₁ sch sch'
control-lemma 
              (Frame (Plus₂ v₁) p₁') (Frame (Plus₂ .v₁) p₂') id₁ c₃ c₄
              (Frame {f₁ = (Plus₂ v₁)}{f₂ = (Plus₂ .v₁)} (Plus₂ .v₁) {c₁ = c₁}{c₂ = c₂} same) e k₁ tr sch sch' = begin

  (cpsTerm (pcontext-plug p₁' (Control id₁ c₃ c₄ e))
       (λ v₂ t₃ →
          CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal v₂))
          (λ v → k₁ (CPSVar v) t₃))
       tr)

  ⟶⟨ control-lemma p₁' p₂' id₁ c₃ c₄ same e
       (λ v₂ t₄ →
          CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal v₂))
          (λ v → k₁ (CPSVar v) t₄))
       tr (λ v t → sLet (λ x → Subst≠) (λ x → sPlu Subst≠ (sVal sVar=)))
       (λ t v₂ → sLet (λ x → sch' t (CPSVar x)) (λ x → Subst≠)) ⟩
  cpsTerm {μs = {!!}}
    (App {μ[γ]β = {!!}} (Val (Fun (λ x → pcontext-plug p₂' (Val (Var x)))))
     (Control {μs₁ = {!!}} id₁ c₃ c₄ e))
    (λ v₂ t₄ →
       CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal v₂))
       (λ v → k₁ (CPSVar v) t₄))
    tr
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ → rApp₁ (rApp₁ (rBeta
      (sVal (sFun (λ x₈ → sVal (sFun (λ x₉ →
      eSubst (subst-context p₂' (Var x))
      (λ x₁₀ → sApp (sApp Subst≠ (sVal x₁₀)) Subst≠))))))))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend c₄ tr (CPSCons c₃ (CPSVar z₁) (CPSVar z₂))))
                 (λ z₃ →
                    CPSApp
                    (CPSApp
                     (CPSVal
                      (CPSFun
                       (λ z₄ →
                          CPSVal
                          (CPSFun
                           (λ z₅ →
                              cpsTerm (pcontext-plug p₂' (Val (Var z)))
                              (λ v t'' →
                                 CPSApp (CPSApp (CPSVal (CPSVar z₄)) (CPSVal v)) (CPSVal t''))
                              (CPSVar z₅))))))
                     (CPSVal
                      (CPSFun
                       (λ v →
                          CPSVal
                          (CPSFun
                           (λ t'' →
                              CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal (CPSVar v)))
                              (λ v₂ → k₁ (CPSVar v₂) (CPSVar t''))))))))
                    (CPSVal (CPSVar z₃))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId)
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ → rApp₁ (rBeta
      (sVal (sFun (λ x₈ →
      kSubst (pcontext-plug p₂' (Val (Var x)))
        (λ y →
           λ v₂ t'''' → CPSApp (CPSApp (CPSVal y) (CPSVal v₂)) (CPSVal t''''))
        (λ x₉ t → sApp (sApp (sVal sVar=) Subst≠) Subst≠)))))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend c₄ tr (CPSCons c₃ (CPSVar z₁) (CPSVar z₂))))
                 (λ z₃ →
                    CPSApp
                    (CPSVal
                     (CPSFun
                      (λ z₄ →
                         cpsTerm (pcontext-plug p₂' (Val (Var z)))
                         (λ v₂ t'''' →
                            CPSApp
                            (CPSApp
                             (CPSVal
                              (CPSFun
                               (λ v →
                                  CPSVal
                                  (CPSFun
                                   (λ t'' →
                                      CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal (CPSVar v)))
                                      (λ v₃ → k₁ (CPSVar v₃) (CPSVar t'')))))))
                             (CPSVal v₂))
                            (CPSVal t''''))
                         (CPSVar z₄))))
                    (CPSVal (CPSVar z₃))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId)
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ → rBeta
      (tSubst (pcontext-plug p₂' (Val (Var x))) (λ t v₂ → sApp Subst≠ (sVal sVar=)))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend c₄ tr (CPSCons c₃ (CPSVar z₁) (CPSVar z₂))))
                 (λ z₃ →
                    cpsTerm (pcontext-plug p₂' (Val (Var z)))
                    (λ v₂ t'''' →
                       CPSApp
                       (CPSApp
                        (CPSVal
                         (CPSFun
                          (λ v →
                             CPSVal
                             (CPSFun
                              (λ t'' →
                                 CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal (CPSVar v)))
                                 (λ v₃ → k₁ (CPSVar v₃) (CPSVar t'')))))))
                        (CPSVal v₂))
                       (CPSVal t''''))
                    (CPSVar z₃)))))))))
    (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId)
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ →
      correctCont (pcontext-plug p₂' (Val (Var x)))
        (λ v₂ t'''' →
           CPSApp
           (CPSApp
            (CPSVal
             (CPSFun
              (λ v₃ →
                 CPSVal
                 (CPSFun
                  (λ t''' →
                     CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal (CPSVar v₃)))
                     (λ v₄ → k₁ (CPSVar v₄) (CPSVar t''')))))))
            (CPSVal v₂))
           (CPSVal t''''))
           {k₂ = (λ v₂ t'''' →
             CPSApp
               (CPSVal
                (CPSFun
                 (λ t''' →
                    CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal v₂))
                    (λ v₄ → k₁ (CPSVar v₄) (CPSVar t''')))))
                    (CPSVal t''''))}
        (λ v t → sApp (sApp Subst≠ (sVal sVar=)) Subst≠)
        λ v t → rApp₁ (rBeta (sVal (sFun (λ x₈ → sLet (λ x₉ → Subst≠)
        (λ x₉ → sPlu Subst≠ (sVal sVar=))))))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend c₄ tr (CPSCons c₃ (CPSVar z₁) (CPSVar z₂))))
                 (λ z₃ →
                    cpsTerm (pcontext-plug p₂' (Val (Var z)))
                    (λ v₂ t'''' →
                       CPSApp
                       (CPSVal
                        (CPSFun
                         (λ t''' →
                            CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal v₂))
                            (λ v₄ → k₁ (CPSVar v₄) (CPSVar t''')))))
                       (CPSVal t''''))
                    (CPSVar z₃)))))))))
    (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId)
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ →
      correctCont (pcontext-plug p₂' (Val (Var x)))
        (λ v₂ t'''' →
           CPSApp
           (CPSVal
            (CPSFun
             (λ t''' →
                CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal v₂))
                (λ v₄ → k₁ (CPSVar v₄) (CPSVar t''')))))
           (CPSVal t''''))
           {k₂ = (λ v₂ t'''' →
               CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal v₂))
               (λ v₄ → k₁ (CPSVar v₄) t''''))}
        (λ v t → sApp (sVal (sFun (λ x₈ → sLet (λ x₉ → Subst≠) (λ x₉ → sPlu Subst≠ (sVal sVar=))))) Subst≠)
        λ v t → rBeta (sLet (λ x₈ → sch' t (CPSVar x₈)) (λ x₈ → Subst≠))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend c₄ tr (CPSCons c₃ (CPSVar z₁) (CPSVar z₂))))
                 (λ z₃ →
                    cpsTerm (pcontext-plug p₂' (Val (Var z)))
                    (λ v₂ t'''' →
                       CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal v₂))
                       (λ v₄ → k₁ (CPSVar v₄) t''''))
                    (CPSVar z₃)))))))))
    (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ →
      correctCont (pcontext-plug p₂' (Val (Var x)))
        (λ v₂ t₄ →
           CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal v₂))
           (λ v₃ →
              CPSApp (CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₃) (CPSVar t'''))))
              (CPSVal t₄)))
              {k₂ = (λ v₂ t₄ →
          CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal v₂))
          (λ v₃ → k₁ (CPSVar v₃) t₄))}
        (λ v t → sLet (λ x₈ → sApp Subst≠ Subst≠) (λ x₈ → sPlu Subst≠ (sVal sVar=)))
        λ v t → rLet₂ (λ x₈ → rBeta (sch' t (CPSVar x₈)))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend c₄ tr (CPSCons c₃ (CPSVar z₁) (CPSVar z₂))))
                 (λ z₃ →
                    cpsTerm (pcontext-plug p₂' (Val (Var z)))
                    (λ v₂ t₄ →
                       CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal v₂))
                       (λ v₃ →
                          CPSApp (CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₃) (CPSVar t'''))))
                          (CPSVal t₄)))
                    (CPSVar z₃)))))))))
    (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ →
      correctCont (pcontext-plug p₂' (Val (Var x)))
        (λ v₂ t₄ →
           CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal v₂))
           (λ v₃ →
              CPSApp
              (CPSApp
               (CPSVal
                (CPSFun
                 (λ v₄ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t'''))))))
               (CPSVal (CPSVar v₃)))
              (CPSVal t₄)))
              {k₂ = (λ v₂ t₄ →
          CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal v₂))
          (λ v₃ →
             CPSApp
              (CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₃) (CPSVar t'''))))
              (CPSVal t₄)))}
        (λ v t → sLet (λ x₈ → sApp Subst≠ Subst≠) (λ x₈ → sPlu Subst≠ (sVal sVar=)))
        λ v t → rLet₂ (λ x₈ → rApp₁ (rBeta (sVal (sFun (λ x₉ → sch (CPSVar x₈) (CPSVar x₉))))))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend c₄ tr (CPSCons c₃ (CPSVar z₁) (CPSVar z₂))))
                 (λ z₃ →
                    cpsTerm (pcontext-plug p₂' (Val (Var z)))
                    (λ v₂ t₄ →
                       CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal v₂))
                       (λ v₃ →
                          CPSApp
                          (CPSApp
                           (CPSVal
                            (CPSFun
                             (λ v₄ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t'''))))))
                           (CPSVal (CPSVar v₃)))
                          (CPSVal t₄)))
                    (CPSVar z₃)))))))))
    (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ → rBeta
      (tSubst (pcontext-plug p₂' (Val (Var x)))
      (λ t v₂ → sLet (λ x₈ → sApp Subst≠ (sVal sVar=)) (λ x₈ → Subst≠)))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend c₄ tr (CPSCons c₃ (CPSVar z₁) (CPSVar z₂))))
                 (λ z₃ →
                    CPSApp
                    (CPSVal
                     (CPSFun
                      (λ z₄ →
                         cpsTerm (pcontext-plug p₂' (Val (Var z)))
                         (λ v₂ t₄ →
                            CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal v₂))
                            (λ v₃ →
                               CPSApp
                               (CPSApp
                                (CPSVal
                                 (CPSFun
                                  (λ v₄ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t'''))))))
                                (CPSVal (CPSVar v₃)))
                               (CPSVal t₄)))
                         (CPSVar z₄))))
                    (CPSVal (CPSVar z₃))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ → rApp₁ (rBeta
      (sVal (sFun (λ x₈ →
      kSubst (pcontext-plug p₂' (Val (Var x)))
        (λ y →
           λ v₂ t₄ →
             CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal v₂))
             (λ v₃ →
                CPSApp (CPSApp (CPSVal y) (CPSVal (CPSVar v₃))) (CPSVal t₄)))
        (λ x₉ t → sLet (λ x₁₀ → sApp (sApp (sVal sVar=) Subst≠) Subst≠) (λ x₁₀ → Subst≠))))))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSLet
                 (CPSVal (CPSAppend c₄ tr (CPSCons c₃ (CPSVar z₁) (CPSVar z₂))))
                 (λ z₃ →
                    CPSApp
                    (CPSApp
                     (CPSVal
                      (CPSFun
                       (λ z₄ →
                          CPSVal
                          (CPSFun
                           (λ z₅ →
                              cpsTerm (pcontext-plug p₂' (Val (Var z)))
                              (λ v₂ t₃ →
                                 CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal v₂))
                                 (λ v₃ →
                                    CPSApp (CPSApp (CPSVal (CPSVar z₄)) (CPSVal (CPSVar v₃)))
                                    (CPSVal t₃)))
                              (CPSVar z₅))))))
                     (CPSVal
                      (CPSFun
                       (λ v₂ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₂) (CPSVar t''')))))))
                    (CPSVal (CPSVar z₃))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₅ → rFun (λ x₆ → rLet₂ (λ x₇ → rApp₁ (rApp₁ (rBeta
      (sVal (sFun (λ x₈ → sVal (sFun (λ x₉ → eSubst (subst-context p₂' (Var x))
      (λ x₁₀ → sLet (λ x₁₁ → sApp Subst≠ Subst≠)
      (λ x₁₁ → sPlu Subst≠ (sVal x₁₀))))))))))))))) ⟩
  (CPSLet
       (CPSVal
        (CPSFun
         (λ v →
            CPSVal
            (CPSFun
             (λ k' →
                CPSVal
                (CPSFun
                 (λ t' →
                    CPSLet
                    (CPSVal (CPSAppend c₄ tr (CPSCons c₃ (CPSVar k') (CPSVar t'))))
                    (λ t'' →
                       CPSApp
                       (CPSApp
                        (CPSApp
                         (CPSVal
                          (CPSFun
                           (λ x →
                              CPSVal
                              (CPSFun
                               (λ k'' →
                                  CPSVal
                                  (CPSFun
                                   (λ t''' →
                                      cpsTerm (pcontext-plug p₂' (Val (Var x)))
                                      (λ v₂ t₃ →
                                         CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal v₂))
                                         (λ v₃ →
                                            CPSApp
                                            (CPSApp (CPSVal (CPSVar k'')) (CPSVal (CPSVar v₃)))
                                            (CPSVal t₃)))
                                      (CPSVar t'''))))))))
                         (CPSVal (CPSVar v)))
                        (CPSVal
                         (CPSFun
                          (λ v₂ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₂) (CPSVar t''')))))))
                       (CPSVal (CPSVar t''))))))))))
       (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId))

  ∎ -}

--一旦凍結
{-
aux₄ : ∀ {var : cpstyp → Set}{τ}{α}{β}{μα}{μβ}{μk}
         {μ[β]α : trails[ μβ ] μα} →
         (e : term[ var ∘ cpsT ] τ ⟨ μ[β]α ⟩ α ⟨ μβ ⟩ β)
         {c : compatible μk μβ μβ}
         (κ : cpsvalue[ var ] (cpsT τ) →  cpsvalue[ var ] (cpsM μα) →
              cpsterm[ var ] (cpsT α))
         (k : var (cpsM μk))
         (t : var (cpsM μβ)) →
         Σ[ c' ∈ compatible μk μα μα ]
         (cpsreduce {var}
         (cpsTerm e
         (λ v t' →
             κ v t')
              (CPSCons c (CPSVar k) (CPSVar t)))
         (cpsTerm e
          (λ v t' →
             κ v (CPSCons c' (CPSVar k) t'))
             (CPSVar t)))

aux₄ (Val v) {c} κ k t = c , r*Id
aux₄ (App e₁ e₂) {c} κ k t = {!!}
aux₄ (Plus e₁ e₂) {c} κ k t = {!!}
aux₄ (Control id₁ c₁ c₂ e) κ k t = {!!}
aux₄ (Prompt id₁ e) κ k t = {!!}-}

--α = βとなっていた
aux-p : ∀ {var : cpstyp → Set}{α}{μα}{μβ}
         {τ} {β}{τ₁}
         {μ[β]α : trails[ μβ ] μα}
         (p : pcontext[ var ∘ cpsT , τ ⟨ [] ⟩ β ⟨ μβ ⟩ β ] τ₁ ⟨ μ[β]α ⟩ α ⟨ μβ ⟩ β)
         (x : var (cpsT τ))
         {c : compatible (τ₁ ⇒ α , μα) μβ μβ}
         (κ : cpsvalue[ var ] (cpsT τ₁) →  cpsvalue[ var ] (cpsM μα) →
              cpsterm[ var ] (cpsT α))
         (k : var (cpsT τ₁ ⇛ (cpsMs μ[β]α ⇛ cpsT α)))
         (t : var (cpsM μβ)) →
        Σ[ c' ∈ compatible (τ₁ ⇒ α , μα) μα μα ]
        (cpsreduce {var}
        (cpsTerm (pcontext-plug p (Val (Var x)))
        (λ v t' →
              κ v t')
         (CPSCons c (CPSVar k) (CPSVar t)))
        (cpsTerm (pcontext-plug p (Val (Var x)))
           (λ v t' →
              κ v (CPSCons c' (CPSVar k) t'))
                (CPSVar t)))

aux-p Hole x {c} κ k t = c , r*Id
aux-p (Frame (App₁ e₂) p) x {c} κ k t = {!!} , {!!}
aux-p (Frame (App₂ v₁) p) x κ k t = {!!}
aux-p (Frame (Plus₁ e₂) p) x κ k t = {!!}
aux-p (Frame (Plus₂ v₁) p) x κ k t = {!!}

aux : ∀ {var} {α} {μα}
        {τ₂} {μ₃}
        {μ[∙]μ₃ : trails[ ∙ ] μ₃}
        {μ[μα]μ₃ : trails[ μα ] μ₃}
        -- {μ[∙]α : trails[ ∙ ] μα} 
        --  {μ[∙]μᵢ : trails[ ∙ ] μᵢ}
        (id : is-id-trails τ₂ α μ[∙]μ₃)
        (z₁ : var (cpsT τ₂ ⇛ (cpsMs μ[μα]μ₃ ⇛ cpsT α)))
        (v : value[ var ∘ cpsT ] τ₂)
        (c : compatible (τ₂ ⇒ α , μ₃) μ₃ μ₃)
        (t' : cpsvalue[ var ] cpsMs μ[μα]μ₃) →
      cpsreduce
      (CPSApp (CPSApp (CPSVal (CPSVar z₁)) (CPSVal (cpsV v)))
       (CPSVal t'))
      (CPSIdk id (cpsV v)
       (CPSCons
        c
        (CPSVar z₁) t'))

aux {μ₃ = τ ⇒ τ' , ∙} id z₁ v (refl , refl , c) t' = begin
  (CPSApp (CPSApp (CPSVal (CPSVar z₁)) (CPSVal (cpsV v)))
       (CPSVal t'))
  ⟵⟨ rApp₂ rConsid ⟩
  CPSApp (CPSApp (CPSVal (CPSVar z₁)) (CPSVal (cpsV v)))
    (CPSVal (CPSCons refl t' CPSId))
  ⟵⟨ rBeta (sApp Subst≠ (sVal (sCon SubstV≠ sVar=))) ⟩
  CPSApp
    (CPSVal
     (CPSFun
      (λ z →
         CPSApp (CPSApp (CPSVal (CPSVar z₁)) (CPSVal (cpsV v)))
         (CPSVal (CPSCons refl t' (CPSVar z))))))
    (CPSVal CPSId)
  ⟵⟨ rApp₁ (rBeta (sVal (sFun (λ x → sApp (sApp Subst≠ (sVal sVar=)) Subst≠)))) ⟩
  CPSApp
    (CPSApp
     (CPSVal
      (CPSFun
       (λ v₁ →
          CPSVal
          (CPSFun
           (λ t'' →
              CPSApp (CPSApp (CPSVal (CPSVar z₁)) (CPSVal (CPSVar v₁)))
              (CPSVal (CPSCons refl t' (CPSVar t''))))))))
     (CPSVal (cpsV v)))
    (CPSVal CPSId)
  ⟵⟨ rApp₁ (rApp₁ rConst) ⟩
  CPSApp
    (CPSApp (CPSVal (CPSCons (refl , refl , c) (CPSVar z₁) t'))
     (CPSVal (cpsV v)))
    (CPSVal CPSId)
  ⟵⟨ rIdkt ⟩
  (CPSIdk id (cpsV v) (CPSCons (refl , refl , c) (CPSVar z₁) t'))

  ∎


------------------------------------------------------------------------------------------------------------------
{-
correctEta : {var : cpstyp → Set} {τ₁ α β : typ} {μα μβ : trail}
             {μs : trails[ μβ ] μα} →
             {e e′ : term[ var ∘ cpsT ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β} →
             (k : cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsMs μs)
             → cpsterm[ var ] (cpsT α)) →
             (t : cpsvalue[ var ] (cpsM μβ)) →
             schematicV k →
             schematicV′ k →
             Reduce e e′ →
             cpsreduce (cpsTerm e k t) (cpsTerm e′ k t)  

correctEta {μs = μs}{e′ = e′} k t sch sch'  (RBeta {e₁ = e₁} {v₂ = v₂} x) = begin
  cpsTerm {μs = μs} (App (Val (Fun e₁)) (Val v₂)) k t
  ⟶⟨ rApp₁ (rApp₁ (rBeta (sVal (sFun (λ x₁ → sVal (sFun (λ x₂ → eSubst  x λ x₃ → sApp (sApp Subst≠ (sVal x₃)) Subst≠))))))) ⟩
  CPSApp
    (CPSApp
     (CPSVal
      (CPSFun
       (λ z →
          CPSVal
          (CPSFun
           (λ z₁ →
              cpsTerm e′
              (λ v t''' →
                 CPSApp (CPSApp (CPSVal (CPSVar z)) (CPSVal v)) (CPSVal t'''))
              (CPSVar z₁))))))
     (CPSVal
      (CPSFun
       (λ v → CPSVal (CPSFun (λ t'' → k (CPSVar v) (CPSVar t'')))))))
    (CPSVal t)
  ⟶⟨ rApp₁ (rBeta (sVal (sFun (λ x₁ → kSubst e′
                                          (λ y →
                                             λ v t''' → CPSApp (CPSApp (CPSVal y) (CPSVal v)) (CPSVal t'''))
                                          (λ x₂ t₁ → sApp (sApp (sVal sVar=) Subst≠)
                                          Subst≠))))) ⟩
  CPSApp
    (CPSVal
     (CPSFun
      (λ z →
         cpsTerm e′
         (λ z₁ z₂ →
            CPSApp
            (CPSApp
             (CPSVal
              (CPSFun
               (λ v → CPSVal (CPSFun (λ t'' → k (CPSVar v) (CPSVar t''))))))
             (CPSVal z₁))
            (CPSVal z₂))
         (CPSVar z))))
    (CPSVal t)
  ⟶⟨ rBeta (tSubst e′ λ t₁ v₃ → sApp Subst≠ (sVal sVar=)) ⟩
  cpsTerm e′
    (λ z₁ z₂ →
       CPSApp
       (CPSApp
        (CPSVal
         (CPSFun
          (λ v → CPSVal (CPSFun (λ t'' → k (CPSVar v) (CPSVar t''))))))
        (CPSVal z₁))
       (CPSVal z₂))
    t
    ⟶⟨ correctCont e′
         (λ z₁ z₂ →
            CPSApp
            (CPSApp
             (CPSVal
              (CPSFun
               (λ v → CPSVal (CPSFun (λ t'' → k (CPSVar v) (CPSVar t''))))))
             (CPSVal z₁))
            (CPSVal z₂))
            {k}
         (λ v t₁ → sApp (sApp Subst≠ (sVal sVar=)) Subst≠)
         (λ v t₁ → (begin
           (CPSApp
       (CPSApp
        (CPSVal
         (CPSFun
          (λ v₁ → CPSVal (CPSFun (λ t'' → k (CPSVar v₁) (CPSVar t''))))))
        (CPSVal (cpsV v)))
       (CPSVal t₁))
        ⟶⟨ rApp₁ (rBeta (sVal (sFun (λ x₁ → sch v (CPSVar x₁))))) ⟩
        CPSApp (CPSVal (CPSFun (λ z → k (cpsV v) (CPSVar z)))) (CPSVal t₁)
        ⟶⟨ rBeta (sch' t₁ (cpsV v)) ⟩
        (k (cpsV v) t₁)
        ∎)) ⟩
  cpsTerm e′ k t
  ∎ 


  
correctEta k t sch sch' (RPlus {τ₂} {μα} {n₁} {n₂}) = begin
  (CPSLet (CPSPlus (CPSVal (CPSNum n₁)) (CPSVal (CPSNum n₂))) (λ v → k (CPSVar v) t))
  ⟶⟨ rLet₁ rPlus ⟩
  CPSLet (CPSVal (CPSNum (n₁ + n₂))) (λ v → k (CPSVar v) t)
  ⟶⟨ rLet (sch (Num (n₁ + n₂)) t) ⟩
  k (CPSNum (n₁ + n₂)) t
  ∎
 
correctEta k t sch sch' (RFrame  (App₁ e₃) x) = correctEta (λ v₁ →
                                                      cpsTerm e₃
                                                      (λ v₂ t₂ →
                                                         CPSApp
                                                         (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
                                                          (CPSVal
                                                           (CPSFun
                                                            (λ v → CPSVal (CPSFun (λ t'' → k (CPSVar v) (CPSVar t'')))))))
                                                         (CPSVal t₂))) t (λ v t₁ →
                                                         kSubst e₃
                                                           (λ x₁ →
                                                              λ v₂ t₂ →
                                                                CPSApp
                                                                (CPSApp (CPSApp (CPSVal x₁) (CPSVal v₂))
                                                                 (CPSVal
                                                                  (CPSFun
                                                                   (λ v₁ → CPSVal (CPSFun (λ t'' → k (CPSVar v₁) (CPSVar t'')))))))
                                                                (CPSVal t₂))
                                                           (λ x₁ t₂ → sApp (sApp (sApp (sVal sVar=) Subst≠)
                                                           Subst≠) Subst≠)) (λ t₁ v₂ → tSubst e₃ λ t₂ v₃ →
                                                           sApp (sApp Subst≠ Subst≠) (sVal sVar=)) x
                                                           
correctEta k t sch sch' (RFrame (App₂ v₁) x) = correctEta (λ v₂ t₂ →
                                                     CPSApp
                                                     (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
                                                      (CPSVal
                                                       (CPSFun
                                                        (λ v → CPSVal (CPSFun (λ t'' → k (CPSVar v) (CPSVar t'')))))))
                                                     (CPSVal t₂)) t
                                                     (λ v t₁ → sApp (sApp (sApp Subst≠ (sVal sVar=))
                                                     Subst≠) Subst≠)
                                                     (λ t₁ v₂ → sApp Subst≠ (sVal sVar=))  x
                                                     
correctEta k t sch sch'  (RFrame (Plus₁ e₃) x) = correctEta (λ v₁ →  cpsTerm e₃
                                                                          (λ v₂ t₂ →
                                                                             CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂))
                                                                             (λ v → k (CPSVar v) t₂))) t
                                                                             (λ v t₁ →
                                                                             kSubst e₃
                                                                               (λ x₁ →
                                                                                  λ v₂ t₂ →
                                                                                    CPSLet (CPSPlus (CPSVal x₁) (CPSVal v₂)) (λ v₁ → k (CPSVar v₁) t₂))
                                                                               (λ x₁ t₂ → sLet (λ x₂ → Subst≠)
                                                                               (λ x₂ → sPlu (sVal sVar=) Subst≠)) )
                                                                                (λ t₁ v₂ → tSubst e₃ λ t₂ v₃ →
                                                                                sLet (λ x₁ → sch' t₂ (CPSVar x₁)) (λ x₁ → Subst≠))  x
                                                  
correctEta k t sch sch'  (RFrame (Plus₂ v₁) x) = correctEta (λ v₂ t₂ →
                                                      CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal v₂))
                                                      (λ v → k (CPSVar v) t₂)) t (λ v t₁ → sLet (λ x₁ → Subst≠)
                                                      (λ x₁ → sPlu Subst≠ (sVal sVar=)))
                                                      (λ t₁ v₂ → sLet (λ x₁ → sch' t₁ (CPSVar x₁))
                                                      λ x₁ → Subst≠)  x
                                                      
correctEta k t sch sch' (RFrame {e₁ = e₁} {e₂ = e₂} (Pro x₁) x) = begin
  (CPSLet (cpsTerm e₁ (CPSIdk x₁) (CPSId))
       (λ v → k (CPSVar v) t))
  ⟶⟨ rLet₁ (correctEta (CPSIdk x₁) (CPSId) (λ v t₁ → sIdk sVar= SubstV≠) (λ t₁ v₂ → sIdk SubstV≠ sVar=) x) ⟩
  (CPSLet (cpsTerm e₂ (CPSIdk x₁) (CPSId))
       (λ v → k (CPSVar v) t))
  ∎
  
correctEta k t sch sch' (RPrompt {v₁ = v₁}) = begin
  (CPSLet (CPSIdk refl (cpsV v₁) (CPSId))
       (λ v → k (CPSVar v) t))
  ⟶⟨ rLet₁ rIdkid ⟩
  CPSLet (CPSVal (cpsV v₁)) (λ v → k (CPSVar v) t)
  ⟶⟨ rLetApp ⟩
  CPSApp (CPSVal (CPSFun (λ v → k (CPSVar v) t))) (CPSVal (cpsV v₁))
  ⟶⟨ rBeta (sch v₁ t) ⟩
  (k (cpsV v₁) t)
  ∎

-- control-lemma : ∀ {var : cpstyp → Set}{τ τ₁ τ₂' τ₅ α β γ γ' t₁ t₂ : typ}
--               {μ₀ μ₂ μ₁ μᵢ μα μβ μα' μγ : trail}
--               --{μ[̇̇∙]α : trails[ ∙ ] μα}
--               {μ[μ₂]μ₁ : trails[ μ₂ ] μ₁}→
--               -- {μ[∙]μ₃ : trails[ ∙ ] μ₃} →
--               {μ[β]μγ : trails[ μβ ] μγ} →
--               {μ[α]μγ : trails[ μα ] μγ} →
--               --{μ[α]μ₃ : trails[ μα ] μ₃} →  
--               {μ[β]α : trails[ μβ ] μα} →
--               {μ[∙]μᵢ : trails[ ∙ ] μᵢ} →
--               (p₁ : pcontext[ var ∘ cpsT , τ ⟨ μ[β]α ⟩ α ⟨ μβ ⟩ β ]
--                             τ₁ ⟨ μ[β]μγ ⟩ τ₅ ⟨ μβ ⟩ β ) →
--               (p₂ : pcontext[ var ∘ cpsT , τ ⟨ []{μα'} ⟩ τ₂' ⟨ μα' ⟩ τ₂' ]
--                             τ₁ ⟨ μ[α]μγ ⟩ τ₅ ⟨ μα ⟩ α ) →
--               --{id₀ : is-id-trails τ₁ τ₅ μ[∙]μ₃} →
--               (id : is-id-trails γ γ' μ[∙]μᵢ) →
--               (c₁ : compatible (t₁ ⇒ t₂ , μ₁) μ₂ μ₀) →
--               (c₂ : compatible μβ μ₀ μα) →
--               same-pcontext p₁ p₂ →
--               (e : var (cpsT (τ ⇒ t₁ ⟨ μ[μ₂]μ₁ ⟩ t₂ ⟨ μ₂ ⟩ α)) →
--                    term[ var ∘ cpsT ] γ ⟨ μ[∙]μᵢ ⟩ γ' ⟨ ∙ ⟩ β) →
--               (k₁ : cpsvalue[ var ] cpsT τ₁ → cpsvalue[ var ] cpsM μγ → cpsterm[ var ] cpsT τ₅) →
--               (tr : cpsvalue[ var ] cpsM μβ) →
--               (sch : schematic k₁) →
--               (sch' : schematicV′ k₁) →
--               cpsreduce
--                 (cpsTerm (pcontext-plug p₁ (Control{μs₁ = μ[μ₂]μ₁} id c₁ c₂ e)) k₁ tr)
--                 (cpsTerm{μs = μ[β]μγ}
--                   (App{μ[γ]β = μ[β]α} (Val (Fun (λ x → pcontext-plug p₂ (Val (Var x)))))
--                   (Control{μs₁ = μ[μ₂]μ₁} id c₁ c₂ e)) k₁ tr)


correctEta {var} {τ₁} {α} {.α} {μα} {.μα} {μs}
           {.(Prompt id₀ (pcontext-plug p₁ (Control id c₁ refl e)))}
           {.(Prompt id (App (Val (Fun e)) (Val (Fun (λ x₂ → pcontext-plug p₂ (Val (Var x₂)))))))}
           k t sch sch'
           (RControl {τ = τ} {γ = γ} {γ' = γ'} {τ₂ = τ₂} {μ[∙]α = μ[∙]α} {μ[∙]μ₃ = μ[∙]μ₃} {μ[μα]μ₃ = μ[μα]μ₃} p₁ p₂ {id₀} id c₁ refl x e) = begin

  (CPSLet
       (cpsTerm (pcontext-plug p₁ (Control id c₁ refl e)) (CPSIdk id₀)
        CPSId)
       (λ v → k (CPSVar v) t))

  ⟶⟨ rLet₁ (control-lemma p₁ p₂ id c₁ refl x e (CPSIdk id₀) CPSId (λ v t₁ → sIdk sVar= SubstV≠)
      λ t₁ v₂ → sIdk SubstV≠ sVar=) ⟩
  CPSLet
    (cpsTerm {μs = μ[∙]μ₃}
     (App {μ[γ]β = μ[∙]α} (Val (Fun (λ x₁ → pcontext-plug p₂ (Val (Var x₁)))))
      (Control {μs₁ = μ[μα]μ₃} id c₁ refl e))
     (CPSIdk id₀) CPSId)
    (λ v → k (CPSVar v) t)
  ⟶⟨ rLet₁ (rLet₁ (rFun (λ x₁ → rFun (λ x₂ → rFun (λ x₃ → rLet₂ (λ x₄ → rApp₁ (rApp₁ (rBeta
      (sVal (sFun (λ x₅ → sVal (sFun (λ x₆ →
      eSubst (subst-context p₂ (Var x₁)) (λ x₇ → sApp (sApp Subst≠ (sVal x₇)) Subst≠)))))))))))))) ⟩
  CPSLet
    (CPSLet
     (CPSVal
      (CPSFun
       (λ z →
          CPSVal
          (CPSFun
           (λ z₁ →
              CPSVal
              (CPSFun
               (λ z₂ →
                  CPSLet
                  (CPSVal
                   (CPSAppend refl CPSId (CPSCons c₁ (CPSVar z₁) (CPSVar z₂))))
                  (λ z₃ →
                     CPSApp
                     (CPSApp
                      (CPSVal
                       (CPSFun
                        (λ z₄ →
                           CPSVal
                           (CPSFun
                            (λ z₅ →
                               cpsTerm (pcontext-plug p₂ (Val (Var z)))
                               (λ v t'' →
                                  CPSApp (CPSApp (CPSVal (CPSVar z₄)) (CPSVal v)) (CPSVal t''))
                               (CPSVar z₅))))))
                      (CPSVal
                       (CPSFun
                        (λ v →
                           CPSVal (CPSFun (λ t'' → CPSIdk id₀ (CPSVar v) (CPSVar t'')))))))
                     (CPSVal (CPSVar z₃))))))))))
     (λ x' → cpsTerm (e x') (CPSIdk id) CPSId))
    (λ v → k (CPSVar v) t)
  ⟶⟨ rLet₁ (rLet₁ (rFun (λ x₁ → rFun (λ x₂ → rFun (λ x₃ → rLet₂ (λ x₄ → rApp₁ (rBeta
      (sVal (sFun (λ x₅ →
      kSubst (pcontext-plug p₂ (Val (Var x₁)))
        (λ y →
           λ v t'' → CPSApp (CPSApp (CPSVal y) (CPSVal v)) (CPSVal t''))
        (λ x₆ t₁ → sApp (sApp (sVal sVar=) Subst≠) Subst≠))))))))))) ⟩
  CPSLet
    (CPSLet
     (CPSVal
      (CPSFun
       (λ z →
          CPSVal
          (CPSFun
           (λ z₁ →
              CPSVal
              (CPSFun
               (λ z₂ →
                  CPSLet
                  (CPSVal
                   (CPSAppend refl CPSId (CPSCons c₁ (CPSVar z₁) (CPSVar z₂))))
                  (λ z₃ →
                     CPSApp
                     (CPSVal
                      (CPSFun
                       (λ z₄ →
                          cpsTerm (pcontext-plug p₂ (Val (Var z)))
                          (λ v t'' →
                             CPSApp
                             (CPSApp
                              (CPSVal
                               (CPSFun
                                (λ v₁ →
                                   CPSVal (CPSFun (λ t''' → CPSIdk id₀ (CPSVar v₁) (CPSVar t'''))))))
                              (CPSVal v))
                             (CPSVal t''))
                          (CPSVar z₄))))
                     (CPSVal (CPSVar z₃))))))))))
     (λ x' → cpsTerm (e x') (CPSIdk id) CPSId))
    (λ v → k (CPSVar v) t)
  ⟶⟨ rLet₁ (rLet₁ (rFun (λ x₁ → rFun (λ x₂ → rFun (λ x₃ → rLet₂ (λ x₄ → rBeta
      (tSubst (pcontext-plug p₂ (Val (Var x₁)))
      (λ t₁ v₂ → sApp Subst≠ (sVal sVar=))))))))) ⟩
  CPSLet
    (CPSLet
     (CPSVal
      (CPSFun
       (λ z →
          CPSVal
          (CPSFun
           (λ z₁ →
              CPSVal
              (CPSFun
               (λ z₂ →
                  CPSLet
                  (CPSVal
                   (CPSAppend refl CPSId (CPSCons c₁ (CPSVar z₁) (CPSVar z₂))))
                  (λ z₃ →
                     cpsTerm (pcontext-plug p₂ (Val (Var z)))
                     (λ v t'' →
                        CPSApp
                        (CPSApp
                         (CPSVal
                          (CPSFun
                           (λ v₁ →
                              CPSVal (CPSFun (λ t''' → CPSIdk id₀ (CPSVar v₁) (CPSVar t'''))))))
                         (CPSVal v))
                        (CPSVal t''))
                     (CPSVar z₃)))))))))
     (λ x' → cpsTerm (e x') (CPSIdk id) CPSId))
    (λ v → k (CPSVar v) t)
  ⟶⟨ rLet₁ (rLet₁ (rFun (λ x₁ → rFun (λ x₂ → rFun (λ x₃ → rLet₂ (λ x₄ →
      correctCont (pcontext-plug p₂ (Val (Var x₁)))
        (λ v t'' →
           CPSApp
           (CPSApp
            (CPSVal
             (CPSFun
              (λ v₁ →
                 CPSVal (CPSFun (λ t''' → CPSIdk id₀ (CPSVar v₁) (CPSVar t'''))))))
            (CPSVal v))
           (CPSVal t''))
        {k₂ =
         λ v t'' →
           CPSApp (CPSVal (CPSFun (λ t''' → CPSIdk id₀ v (CPSVar t'''))))
           (CPSVal t'')}
        (λ v t₁ → sApp (sApp Subst≠ (sVal sVar=)) Subst≠)
        (λ v t₁ → rApp₁ (rBeta (sVal (sFun (λ x₅ → sIdk sVar= SubstV≠))))))))))) ⟩
  CPSLet
    (CPSLet
     (CPSVal
      (CPSFun
       (λ z →
          CPSVal
          (CPSFun
           (λ z₁ →
              CPSVal
              (CPSFun
               (λ z₂ →
                  CPSLet
                  (CPSVal
                   (CPSAppend refl CPSId (CPSCons c₁ (CPSVar z₁) (CPSVar z₂))))
                  (λ z₃ →
                     cpsTerm (pcontext-plug p₂ (Val (Var z)))
                     (λ v t'' →
                        CPSApp (CPSVal (CPSFun (λ t''' → CPSIdk id₀ v (CPSVar t'''))))
                        (CPSVal t''))
                     (CPSVar z₃)))))))))
     (λ x' → cpsTerm (e x') (CPSIdk id) CPSId))
    (λ v → k (CPSVar v) t)
  ⟶⟨ rLet₁ (rLet₁ (rFun (λ x₁ → rFun (λ x₂ → rFun (λ x₃ → rLet₂ (λ x₄ →
      correctCont (pcontext-plug p₂ (Val (Var x₁)))
        (λ v t'' →
           CPSApp (CPSVal (CPSFun (λ t''' → CPSIdk id₀ v (CPSVar t'''))))
           (CPSVal t''))
        {k₂ = λ v t'' → CPSIdk id₀ v t''}
        (λ v t₁ → sApp (sVal (sFun (λ x₅ → sIdk sVar= SubstV≠))) Subst≠)
        (λ v t₁ → rBeta (sIdk SubstV≠ sVar=)))))))) ⟩
  CPSLet
    (CPSLet
     (CPSVal
      (CPSFun
       (λ z →
          CPSVal
          (CPSFun
           (λ z₁ →
              CPSVal
              (CPSFun
               (λ z₂ →
                  CPSLet
                  (CPSVal
                   (CPSAppend refl CPSId (CPSCons c₁ (CPSVar z₁) (CPSVar z₂))))
                  (λ z₃ →
                     cpsTerm (pcontext-plug p₂ (Val (Var z)))
                     (λ v t'' → CPSIdk id₀ v t'') (CPSVar z₃)))))))))
     (λ x' → cpsTerm (e x') (CPSIdk id) CPSId))
    (λ v → k (CPSVar v) t)
  ⟶⟨ rLet₁ (rLet₁ (rFun (λ x₁ → rFun (λ x₂ → rFun (λ x₃ → rLet₁ rApdid))))) ⟩
  CPSLet
    (CPSLet
     (CPSVal
      (CPSFun
       (λ z →
          CPSVal
          (CPSFun
           (λ z₁ →
              CPSVal
              (CPSFun
               (λ z₂ →
                  CPSLet (CPSVal (CPSCons c₁ (CPSVar z₁) (CPSVar z₂)))
                  (λ z₃ →
                     cpsTerm (pcontext-plug p₂ (Val (Var z)))
                     (λ v t'' → CPSIdk id₀ v t'') (CPSVar z₃)))))))))
     (λ x' → cpsTerm (e x') (CPSIdk id) CPSId))
    (λ v → k (CPSVar v) t)
  ⟶⟨ rLet₁ (rLet₁ (rFun (λ x₁ → rFun (λ x₂ → rFun (λ x₃ → rLetApp))))) ⟩
  CPSLet
    (CPSLet
     (CPSVal
      (CPSFun
       (λ z →
          CPSVal
          (CPSFun
           (λ z₁ →
              CPSVal
              (CPSFun
               (λ z₂ →
                  CPSApp
                  (CPSVal
                   (CPSFun
                    (λ z₃ →
                       cpsTerm (pcontext-plug p₂ (Val (Var z)))
                       (λ v t'' → CPSIdk id₀ v t'') (CPSVar z₃))))
                  (CPSVal (CPSCons c₁ (CPSVar z₁) (CPSVar z₂))))))))))
     (λ x' → cpsTerm (e x') (CPSIdk id) CPSId))
    (λ v → k (CPSVar v) t)
  ⟶⟨ rLet₁ (rLet₁ (rFun (λ x₁ → rFun (λ x₂ → rFun (λ x₃ → rBeta
      (tSubst (pcontext-plug p₂ (Val (Var x₁))) (λ t₁ v₂ → sIdk SubstV≠ sVar=))))))) ⟩
  CPSLet
    (CPSLet
     (CPSVal
      (CPSFun
       (λ z →
          CPSVal
          (CPSFun
           (λ z₁ →
              CPSVal
              (CPSFun
               (λ z₂ →
                  cpsTerm (pcontext-plug p₂ (Val (Var z))) (CPSIdk id₀)
                  (CPSCons c₁ (CPSVar z₁) (CPSVar z₂)))))))))
     (λ x' → cpsTerm (e x') (CPSIdk id) CPSId))
    (λ v → k (CPSVar v) t)
    --aux-p version
    ⟶⟨ rLet₁ (rLet₁ (rFun (λ x₁ → rFun (λ x₂ → rFun (λ x₃ → proj₂ (aux-p p₂ x₁ (CPSIdk id₀) x₂ x₃)))))) ⟩
    CPSLet
      (CPSLet
       (CPSVal
        (CPSFun
         (λ z →
            CPSVal
            (CPSFun
             (λ z₁ →
                CPSVal
                (CPSFun
                 (λ z₂ →
                    cpsTerm (pcontext-plug p₂ (Val (Var z)))
                    (λ v t' →
                       CPSIdk id₀ v
                       (CPSCons (proj₁ (aux-p {var} p₂ z {c = c₁} (CPSIdk id₀) z₁ z₂)) (CPSVar z₁) t'))
                    (CPSVar z₂))))))))
       (λ x' → cpsTerm (e x') (CPSIdk id) CPSId))
      (λ v → k (CPSVar v) t)
    ⟵⟨ rLet₁ (rLet₁ (rFun (λ x₁ → rFun (λ x₂ → rFun (λ x₃ →
                    correctCont (pcontext-plug p₂ (Val (Var x₁)))
                      (λ v t'' →
                         CPSApp (CPSApp (CPSVal (CPSVar x₂)) (CPSVal v)) (CPSVal t''))
                      {k₂ =
                       λ v t'' →
                         CPSIdk id₀ v
                         (CPSCons (proj₁ (aux-p {var} p₂ x₁ {c = c₁} (CPSIdk id₀) x₂ x₃)) (CPSVar x₂) t'')}
                      (λ v t₁ → sApp (sApp Subst≠ (sVal sVar=)) Subst≠)
                      (λ v t₁ → aux {μ[∙]μ₃ = μ[∙]μ₃} {μ[μα]μ₃ = μ[μα]μ₃} id₀ x₂ v (proj₁ (aux-p {var}  p₂ x₁ {c = c₁} (CPSIdk id₀) x₂ x₃)) t₁)))))) ⟩
  --aux₄ varsion
  -- ⟶⟨ rLet₁ (rLet₁ (rFun (λ x₁ → rFun (λ x₂ → rFun (λ x₃ → proj₂ (aux₄ (pcontext-plug p₂ (Val (Var x₁))) (CPSIdk id₀) x₂ x₃) ))))) ⟩
  -- CPSLet
  --   (CPSLet
  --    (CPSVal
  --     (CPSFunc
  --      (λ z →
  --         CPSVal
  --         (CPSFun
  --          (λ z₁ →
  --             CPSVal
  --             (CPSFun
  --              (λ z₂ →
  --                 cpsTerm (pcontext-plug p₂ (Val (Var z)))
  --                 (λ v t'' → CPSIdk id₀ v (CPSCons (proj₁ (aux₄ {var} (pcontext-plug p₂ (Val (Var z))) {c = c₁} (CPSIdk id₀) z₁ z₂)) (CPSVar z₁) t''))
  --                 (CPSVar z₂))))))))
  --    (λ x' → cpsTerm (e x') (CPSIdk id) CPSId))
  --   (λ v → k (CPSVar v) t)
  -- ⟵⟨ rLet₁ (rLet₁ (rFun (λ x₁ → rFun (λ x₂ → rFun (λ x₃ →
  --          correctCont (pcontext-plug p₂ (Val (Var x₁)))
  --            (λ v t'' →
  --               CPSApp (CPSApp (CPSVal (CPSVar x₂)) (CPSVal v)) (CPSVal t''))
  --            {k₂ = λ v t'' → CPSIdk id₀ v (CPSCons ((proj₁ (aux₄ {var} (pcontext-plug p₂ (Val (Var x₁))) {c = c₁} (CPSIdk id₀) x₂ x₃))) (CPSVar x₂) t'')}
  --            (λ v t₁ → sApp (sApp Subst≠ (sVal sVar=)) Subst≠) λ v t₁ → aux {μ[∙]μ₃ = μ[∙]μ₃} {μ[μα]μ₃ = μ[μα]μ₃} id₀ x₂ v (proj₁ (aux₄ {var} (pcontext-plug p₂ (Val (Var x₁))) {c = c₁} (CPSIdk id₀) x₂ x₃)) t₁))))) ⟩
  CPSLet
    (CPSLet
     (CPSVal
      (CPSFun
       (λ x₁ →
          CPSVal
          (CPSFun
           (λ k' →
              CPSVal
              (CPSFun
               (λ t' →
                  cpsTerm (pcontext-plug p₂ (Val (Var x₁)))
                  (λ v t'' →
                     CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                  (CPSVar t'))))))))
     (λ z → cpsTerm (e z) (CPSIdk id) CPSId))
    (λ v → k (CPSVar v) t)
  ≡⟨ refl ⟩
  CPSLet
    (CPSLet
     (CPSVal
      (CPSFun
       (λ x₁ →
          CPSVal
          (CPSFun
           (λ k' →
              CPSVal
              (CPSFun
               (λ t' →
                  cpsTerm (pcontext-plug p₂ (Val (Var x₁)))
                  (λ v t'' →
                     CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                  (CPSVar t'))))))))
     (λ z → cpsTerm (e z) (λ v t'' → CPSIdk id v t'') CPSId))
    (λ v → k (CPSVar v) t)
  ⟵⟨ rLet₁ (rLet₂ (λ x₁ →
      correctCont (e x₁)
        (λ v t'' →
           CPSApp (CPSVal (CPSFun (λ t''' → CPSIdk id v (CPSVar t'''))))
           (CPSVal t''))
        {k₂ = λ v t'' → CPSIdk id v t''} (λ v t₁ →
        sApp (sVal (sFun (λ x₂ → sIdk sVar= SubstV≠))) Subst≠)
        (λ v t₁ → rBeta (sIdk SubstV≠ sVar=)))) ⟩
  CPSLet
    (CPSLet
     (CPSVal
      (CPSFun
       (λ x₁ →
          CPSVal
          (CPSFun
           (λ k' →
              CPSVal
              (CPSFun
               (λ t' →
                  cpsTerm (pcontext-plug p₂ (Val (Var x₁)))
                  (λ v t'' →
                     CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                  (CPSVar t'))))))))
     (λ z →
        cpsTerm (e z)
        (λ v t'' →
           CPSApp (CPSVal (CPSFun (λ t''' → CPSIdk id v (CPSVar t'''))))
           (CPSVal t''))
        CPSId))
    (λ v → k (CPSVar v) t)
  ⟵⟨ rLet₁ (rLet₂ (λ x₁ →
      correctCont (e x₁)
        (λ v t'' →
           CPSApp
           (CPSApp
            (CPSVal
             (CPSFun
              (λ v₁ →
                 CPSVal (CPSFun (λ t''' → CPSIdk id (CPSVar v₁) (CPSVar t'''))))))
            (CPSVal v))
           (CPSVal t''))
        {k₂ =
         λ v t'' →
           CPSApp (CPSVal (CPSFun (λ t''' → CPSIdk id v (CPSVar t'''))))
           (CPSVal t'')}
        (λ v t₁ → sApp (sApp Subst≠ (sVal sVar=)) Subst≠)
        (λ v t₁ → rApp₁ (rBeta (sVal (sFun (λ x₂ → sIdk sVar= SubstV≠))))))) ⟩
  CPSLet
    (CPSLet
     (CPSVal
      (CPSFun
       (λ x₁ →
          CPSVal
          (CPSFun
           (λ k' →
              CPSVal
              (CPSFun
               (λ t' →
                  cpsTerm (pcontext-plug p₂ (Val (Var x₁)))
                  (λ v t'' →
                     CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                  (CPSVar t'))))))))
     (λ z →
        cpsTerm (e z)
        (λ v t'' →
           CPSApp
           (CPSApp
            (CPSVal
             (CPSFun
              (λ v₁ →
                 CPSVal (CPSFun (λ t''' → CPSIdk id (CPSVar v₁) (CPSVar t'''))))))
            (CPSVal v))
           (CPSVal t''))
        CPSId))
    (λ v → k (CPSVar v) t)
  ⟵⟨ rLet₁ (rLet₂ (λ x₁ → rBeta (tSubst (e x₁) (λ t₁ v₂ → sApp Subst≠ (sVal sVar=))))) ⟩
  CPSLet
    (CPSLet
     (CPSVal
      (CPSFun
       (λ x₁ →
          CPSVal
          (CPSFun
           (λ k' →
              CPSVal
              (CPSFun
               (λ t' →
                  cpsTerm (pcontext-plug p₂ (Val (Var x₁)))
                  (λ v t'' →
                     CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                  (CPSVar t'))))))))
     (λ x₁ →
        CPSApp
        (CPSVal
         (CPSFun
          (λ z₁ →
             cpsTerm (e x₁)
             (λ v t'' →
                CPSApp
                (CPSApp
                 (CPSVal
                  (CPSFun
                   (λ v₁ →
                      CPSVal (CPSFun (λ t''' → CPSIdk id (CPSVar v₁) (CPSVar t'''))))))
                 (CPSVal v))
                (CPSVal t''))
             (CPSVar z₁))))
        (CPSVal CPSId)))
    (λ v → k (CPSVar v) t)
  ⟵⟨ rLet₁ rLet₃ ⟩
  CPSLet
    (CPSApp
     (CPSLet
      (CPSVal
       (CPSFun
        (λ x₁ →
           CPSVal
           (CPSFun
            (λ k' →
               CPSVal
               (CPSFun
                (λ t' →
                   cpsTerm (pcontext-plug p₂ (Val (Var x₁)))
                   (λ v t'' →
                      CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                   (CPSVar t'))))))))
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             cpsTerm (e z)
             (λ v t'' →
                CPSApp
                (CPSApp
                 (CPSVal
                  (CPSFun
                   (λ v₁ →
                      CPSVal (CPSFun (λ t''' → CPSIdk id (CPSVar v₁) (CPSVar t'''))))))
                 (CPSVal v))
                (CPSVal t''))
             (CPSVar z₁)))))
     (CPSVal CPSId))
    (λ v → k (CPSVar v) t)
  ⟵⟨ rLet₁ (rApp₁ (rLet₂ (λ x₁ → rBeta (sVal (sFun (λ x₂ →
      kSubst (e x₁)
        (λ y →
           λ v t'' → CPSApp (CPSApp (CPSVal y) (CPSVal v)) (CPSVal t''))
        (λ x₃ t₁ → sApp (sApp (sVal sVar=) Subst≠) Subst≠))))))) ⟩
  CPSLet
    (CPSApp
     (CPSLet
      (CPSVal
       (CPSFun
        (λ x₁ →
           CPSVal
           (CPSFun
            (λ k' →
               CPSVal
               (CPSFun
                (λ t' →
                   cpsTerm (pcontext-plug p₂ (Val (Var x₁)))
                   (λ v t'' →
                      CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                   (CPSVar t'))))))))
      (λ x₁ →
         CPSApp
         (CPSVal
          (CPSFun
           (λ k' →
              CPSVal
              (CPSFun
               (λ t' →
                  cpsTerm (e x₁)
                  (λ v t'' →
                     CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                  (CPSVar t'))))))
         (CPSVal
          (CPSFun
           (λ v →
              CPSVal (CPSFun (λ t'' → CPSIdk id (CPSVar v) (CPSVar t''))))))))
     (CPSVal CPSId))
    (λ v → k (CPSVar v) t)
  ⟵⟨ rLet₁ (rApp₁ rLet₃) ⟩
  CPSLet
    (CPSApp
     (CPSApp
      (CPSLet
       (CPSVal
        (CPSFun
         (λ x₁ →
            CPSVal
            (CPSFun
             (λ k' →
                CPSVal
                (CPSFun
                 (λ t' →
                    cpsTerm (pcontext-plug p₂ (Val (Var x₁)))
                    (λ v t'' →
                       CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                    (CPSVar t'))))))))
       (λ x₁ →
          CPSVal
          (CPSFun
           (λ k' →
              CPSVal
              (CPSFun
               (λ t' →
                  cpsTerm (e x₁)
                  (λ v t'' →
                     CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                  (CPSVar t')))))))
      (CPSVal
       (CPSFun
        (λ v →
           CPSVal (CPSFun (λ t'' → CPSIdk id (CPSVar v) (CPSVar t'')))))))
     (CPSVal CPSId))
    (λ v → k (CPSVar v) t)
  ⟶⟨ rLet₁ (rApp₁ (rApp₁ rLetApp)) ⟩
  (CPSLet
       (CPSApp
        (CPSApp
         (CPSApp
          (CPSVal
           (CPSFun
            (λ x₁ →
               CPSVal
               (CPSFun
                (λ k' →
                   CPSVal
                   (CPSFun
                    (λ t' →
                       cpsTerm (e x₁)
                       (λ v t'' →
                          CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                       (CPSVar t'))))))))
          (CPSVal
           (CPSFun
            (λ x₁ →
               CPSVal
               (CPSFun
                (λ k' →
                   CPSVal
                   (CPSFun
                    (λ t' →
                       cpsTerm (pcontext-plug p₂ (Val (Var x₁)))
                       (λ v t'' →
                          CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                       (CPSVar t')))))))))
         (CPSVal
          (CPSFun
           (λ v →
              CPSVal (CPSFun (λ t'' → CPSIdk id (CPSVar v) (CPSVar t'')))))))
        (CPSVal CPSId))
       (λ v → k (CPSVar v) t))

  ∎-}

