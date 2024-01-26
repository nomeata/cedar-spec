permit(
  principal == A::a::"",
  action,
  resource is A::a in A::a::""
) when {
  true && (principal has "")
};
