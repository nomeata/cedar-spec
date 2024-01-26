permit(
  principal == A00zl::a::"j",
  action in [A00zl::Action::"action"],
  resource == A00zl::a::"j"
) when {
  (true && (([true, context, A00zl::a::"j"].contains(true)) == A00zl::a::"j")) && action
};
