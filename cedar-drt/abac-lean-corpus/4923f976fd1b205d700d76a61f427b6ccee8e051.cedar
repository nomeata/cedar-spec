permit(
  principal == a::"",
  action in [Action::"action"],
  resource in a::"j"
) when {
  (true && resource) && (false in ((false in false) in (false in false)))
};
