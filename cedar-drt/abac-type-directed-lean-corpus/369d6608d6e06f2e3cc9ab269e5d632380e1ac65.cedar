permit(
  principal == a::"666",
  action,
  resource
) when {
  ((true && ((if ([] == []) then [] else []).containsAny([]))) && (a::"666" in a::"")) && (!(principal is a))
};
