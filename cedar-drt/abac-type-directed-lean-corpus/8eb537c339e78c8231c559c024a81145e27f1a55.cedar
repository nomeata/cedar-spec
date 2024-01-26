permit(
  principal == A::"",
  action,
  resource is A in A::""
) when {
  true && (action has "")
};
