permit(
  principal == a::"8",
  action,
  resource == a::"8"
) when {
  ((true && [a::"8", a::"8", !(!a::"8"), !(!a::"8")]) && (!(!(!a::"8")))) && (!context)
};
