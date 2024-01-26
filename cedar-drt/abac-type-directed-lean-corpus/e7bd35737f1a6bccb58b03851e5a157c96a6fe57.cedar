permit(
  principal is a in a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  (true && (a::"6\t" in principal)) && false
};
