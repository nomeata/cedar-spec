permit(
  principal,
  action == A::Action::"action",
  resource in A::a::""
) when {
  ((true && (resource in resource)) && (resource in resource)) && ((if (action in action) then (decimal("\u{1}")) else (decimal("!"))) == (decimal("")))
};
