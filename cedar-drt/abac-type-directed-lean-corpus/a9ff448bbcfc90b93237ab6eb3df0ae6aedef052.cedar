permit(
  principal,
  action in [A::Action::"action"],
  resource is A::r in A::r::""
) when {
  ((true && (action in action)) && (A::r::"" in principal)) && true
};
