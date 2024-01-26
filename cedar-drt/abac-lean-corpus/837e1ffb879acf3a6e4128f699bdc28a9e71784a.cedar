forbid(
  principal is a,
  action in [Action::"action"],
  resource
) when {
  true && (((Action::"action" == false) == true) == true)
};
