@r("")
forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  ((true && a::"\0\0\0") && (a::"\0\0\0" in principal)) && principal
};
