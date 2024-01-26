permit(
  principal == a::"mpl",
  action in [Action::"action"],
  resource == a::"mpl"
) when {
  (true && (([false, a::"", Action::"action"].containsAll(70368284616190570)) == false)) && principal
};
