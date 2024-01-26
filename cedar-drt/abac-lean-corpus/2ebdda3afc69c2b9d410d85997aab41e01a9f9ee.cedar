permit(
  principal == a::"j",
  action in [Action::"action"],
  resource == a::"j"
) when {
  (true && (([false, a::"j", Ahhch::"\0\0\0"].containsAll("xj")) == [action == false, a::"" in action])) && a::""
};
