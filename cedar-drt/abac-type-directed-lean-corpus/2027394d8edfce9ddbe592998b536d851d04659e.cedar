permit(
  principal,
  action == A::Action::"action",
  resource in A::a::""
) when {
  (true && (resource in resource)) && (resource in resource)
};
