permit(
  principal == a::"",
  action == Action::"action",
  resource is a
) when {
  (true && [a::"", principal, !((!(Action::"action" < Action::"action")) < (!(Action::"action" < Action::"action"))), !((!(Action::"action" < Action::"action")) < (!(Action::"action" < Action::"action"))), !((!(Action::"action" < Action::"action")) < (!(Action::"action" < true))), Action::"action"]) && (!((!((!(Action::"action" < Action::"action")) < (!(Action::"action" < false)))) < principal))
};
