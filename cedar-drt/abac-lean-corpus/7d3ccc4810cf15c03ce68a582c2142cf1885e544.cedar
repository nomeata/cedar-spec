permit(
  principal == a::"",
  action in [Action::"action"],
  resource
) when {
  ((true && "") && Action::"action") && (!a::"")
};
