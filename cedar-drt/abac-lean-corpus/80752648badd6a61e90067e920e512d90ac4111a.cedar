@Sglh("")
permit(
  principal,
  action,
  resource
) when {
  true && {"A": Action::"action"}
};
