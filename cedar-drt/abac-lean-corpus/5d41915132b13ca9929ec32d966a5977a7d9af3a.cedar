forbid(
  principal,
  action in [Action::""],
  resource
) when {
  ((true && ((if (Action::"" has "") then action else zhh00::"") has "")) && principal) && principal
};
