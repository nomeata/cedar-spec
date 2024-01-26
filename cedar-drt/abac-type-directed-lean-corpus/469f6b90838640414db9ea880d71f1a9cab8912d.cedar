permit(
  principal in A::a::"\n\0\0\0\0\0\0\0",
  action in [A::Action::"action",A::Action::"action",A::Action::"action"],
  resource
) when {
  true && (action has "")
};
