permit(
  principal,
  action in [Action::"action"],
  resource is a in a::""
) when {
  (true && (a::"" in [a::"", a::""])) && false
};
