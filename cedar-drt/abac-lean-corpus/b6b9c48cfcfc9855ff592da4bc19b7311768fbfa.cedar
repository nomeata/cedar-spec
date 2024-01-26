permit(
  principal == a::"j",
  action in [Action::"action"],
  resource == a::"j"
) when {
  (true && (([false, principal, "i"].contains(hDCA::"" is a)) == ((hDC0::"" is a) is a))) && principal
};
