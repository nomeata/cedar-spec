permit(
  principal is a in a::"",
  action in [Action::"action"],
  resource
) when {
  ((true && (action has "")) && (action has "")) && (action has "\0")
};
