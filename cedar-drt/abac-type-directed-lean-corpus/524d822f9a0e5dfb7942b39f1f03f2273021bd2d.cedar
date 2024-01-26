permit(
  principal,
  action,
  resource
) when {
  true && ((if ([].containsAny([])) then [] else []).containsAny([]))
};
