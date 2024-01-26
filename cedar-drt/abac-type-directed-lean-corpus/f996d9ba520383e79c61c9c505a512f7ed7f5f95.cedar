permit(
  principal in a::"6",
  action in [Action::"action"],
  resource in a::"6"
) when {
  (true && (({"": decimal("504744192441291.77966")}[""]).lessThan(decimal("")))) && (Action::"action" in action)
};
