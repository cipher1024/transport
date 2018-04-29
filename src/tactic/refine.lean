
import data.dlist
import util.control.applicative

def dlist.join {α} : list (dlist α) → dlist α
 | [] := dlist.empty
 | (x :: xs) := x ++ dlist.join xs

namespace tactic

open interactive interactive.types lean.parser
     tactic.interactive (itactic)
     tactic nat applicative

meta def var_names : expr → list name
 | (expr.pi n _ _ b) := n :: var_names b
 | _ := []

meta def drop_binders : expr → tactic expr
 | (expr.pi n bi t b) := b.instantiate_var <$> mk_local' n bi t >>= drop_binders
 | e := pure e

meta def subobject_names (struct_n : name) : tactic (list name × list name) :=
do env ← get_env,
   [c] ← pure $ env.constructors_of struct_n | fail "too many constructors",
   vs  ← var_names <$> (mk_const c >>= infer_type),
   fields ← env.structure_fields struct_n,
   return $ fields.partition (λ fn, ↑("_" ++ fn.to_string) ∈ vs)

meta def expanded_field_list' : name → tactic (dlist $ name × name) | struct_n :=
do (so,fs) ← subobject_names struct_n,
   ts ← so.mmap (λ n, do
     e ← mk_const (n.update_prefix struct_n) >>= infer_type >>= drop_binders,
     expanded_field_list' $ e.get_app_fn.const_name),
   -- trace so, trace fs,
   return $ dlist.join ts ++ dlist.of_list (fs.map $ prod.mk struct_n)

meta def expanded_field_list (struct_n : name) : tactic (list $ name × name) :=
dlist.to_list <$> expanded_field_list' struct_n

meta def mk_mvar_list : ℕ → tactic (list expr)
 | 0 := pure []
 | (succ n) := (::) <$> mk_mvar <*> mk_mvar_list n

namespace interactive

meta def refineS (e : parse texpr) (ph : parse $ optional $ tk "with" *> ident) : tactic unit :=
do    str ← e.get_structure_instance_info,
      tgt ← target,
      let struct_n : name := tgt.get_app_fn.const_name,
      exp_fields ← expanded_field_list struct_n,
      let exp_fields' := exp_fields.map prod.snd,
      let missing_f := exp_fields.filter (λ f, (f.2 : name) ∉ str.field_names),
      let provided := exp_fields.filter (λ f, (f.2 : name) ∈ str.field_names),
      vs ← mk_mvar_list missing_f.length,
      let e' : pexpr := pexpr.mk_structure_instance
          { struct := some struct_n
          , field_names := str.field_names ++ missing_f.map prod.snd
          , field_values := str.field_values ++ vs.map to_pexpr },
      refine e',
      gs ← with_enable_tags (
        mmap₂ (λ (n : name × name) v, do
           set_goals [v],
           try (interactive.unfold (provided.map $ λ ⟨s,f⟩, f.update_prefix s) (loc.ns [none])),
           apply_auto_param
             <|> apply_opt_param
             <|> (do match ph with
                       | (some ph) := () <$ (mk_const (n.2.update_prefix n.1) >>= pose ph none)
                       | none := return ()
                     end,
                     set_main_tag [`_field,n.2]),
           get_goals)
        missing_f vs),
      set_goals gs.join

meta def collect_tagged_goals (pre : name) : tactic (list expr) :=
do gs ← get_goals,
   gs.mfoldr (λ g r, do
      pre' :: t ← get_tag g,
      if t = [pre] ∧ pre' = pre'.get_prefix <.> "_field"
         then return (g::r)
         else return r)
      []

-- meta def match_field_tag

meta def field (tag : parse ident) (tac : itactic) : tactic unit :=
do ts ← collect_tagged_goals tag,
   match ts with
    | [] := fail format!"no field goal with tag {tag}"
    | [g] := do
      gs ← get_goals,
      set_goals $ g :: gs.filter (≠ g),
      solve1 tac
    | _ := fail format!"multiple goals have tag {tag}"
   end

end interactive

end tactic
