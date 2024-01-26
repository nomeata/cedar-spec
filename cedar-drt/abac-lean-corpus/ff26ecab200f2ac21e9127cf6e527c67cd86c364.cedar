forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  (true && ((!(context <= a::"")) in Action::"action")) && (((!Action::"action") in (!Action::"action")) in false)
};
