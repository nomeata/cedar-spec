permit(
  principal is A::a in A::a::">6",
  action in [A::Action::"action"],
  resource is A::a in A::a::">6"
) when {
  true && (action has "")
};
