@Ehhf0000e1OjO("x")
permit(
  principal == a::"",
  action in [Action::"action"],
  resource
) when {
  true && (true.lessThan(A::"", action, a::"" in (if principal then principal else principal)))
};
