@l("")
permit(
  principal in a::"",
  action in [Action::"policies"],
  resource
) when {
  (true && Action::"policies") && true
};
