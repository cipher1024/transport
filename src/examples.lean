import transport

open tactic tactic.interactive

meta def isolate {α} (tac : tactic α) : tactic unit :=
do e ← get_env,
   tac,
   set_env e

-- set_option profiler true

-- run_cmd do
--  mk_transportable_instance `group
-- run_cmd do
--  mk_transportable_instance `monoid
-- run_cmd do
--  mk_transportable_instance `ring
-- run_cmd do
--  mk_transportable_instance `field

-- run_cmd do
--  mk_to_fun `group
-- run_cmd do
--  mk_to_fun `monoid

-- set_option pp.notation false
set_option trace.app_builder true

-- run_cmd do
--  mk_to_fun `ring
run_cmd do
 mk_to_fun `field

-- run_cmd do
--  mk_to_fun `group >>= mk_on_equiv `group
-- run_cmd do
--  mk_to_fun `monoid >>= mk_on_equiv `monoid
-- run_cmd do
--  mk_to_fun `ring >>= mk_on_equiv `ring
-- run_cmd do
--  mk_to_fun `field >>= mk_on_equiv `field

-- attribute [derive transportable] group
-- attribute [derive transportable] monoid
-- attribute [derive transportable] ring
-- attribute [derive transportable] field
