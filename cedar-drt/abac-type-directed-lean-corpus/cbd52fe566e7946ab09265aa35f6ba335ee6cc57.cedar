permit(
  principal,
  action in [A::Action::"action"],
  resource is A::a in A::a::""
) when {
  false
};
