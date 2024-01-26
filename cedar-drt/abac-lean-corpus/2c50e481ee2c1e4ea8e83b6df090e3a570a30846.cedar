permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  (true && (([] == Q0008::_gglDjhhhmh::"pj").containsAny([Action::"action", action]))) && (((principal == action) == true) == (!Action::"action"))
};
