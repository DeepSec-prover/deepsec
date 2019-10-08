open Process_simulator

val find_equivalent_trace :
  Process.semantics ->
  trace ->
  process ->
  process ->
  trace option
