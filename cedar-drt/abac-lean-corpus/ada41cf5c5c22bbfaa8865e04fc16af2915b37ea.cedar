permit(
  principal == A::a::"i",
  action in [A::Action::"action",A::Action::"action"],
  resource is A::a in A::a::"i"
) when {
  (true && (context in ([] in (A::Action::"action" in A::Action::"action")))) && (((false in A::a::"") in A::a::"i") in "")
};
