permit(
  principal is B::a,
  action in [B::Action::"action"],
  resource is B::a in B::a::""
) when {
  false
};
