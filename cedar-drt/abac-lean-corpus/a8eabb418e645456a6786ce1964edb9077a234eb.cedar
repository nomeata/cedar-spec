permit(
  principal == a::"",
  action in [Action::"action"],
  resource == a::"\0\u{4}"
) when {
  ((true && (((false == principal) == Action::"action") == a::"")) && Action::"action") && Action::"action"
};
