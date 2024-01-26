permit(
  principal is a in a::"j",
  action in [Action::"action"],
  resource is a in a::"j"
) when {
  (true && (Action::"action" && ((Action::"action" in Action::"action") + (Action::"action" in Action::"action")))) && ((Action::"action" == (Action::"action" + Action::"action")) in ((C0000::"" + principal) in principal))
};
